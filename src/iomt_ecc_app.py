#!/usr/bin/env python3
# =============================================================================
#  IoMT-ECC Secure System — Application de simulation complète
#  Cryptographie ECC + IA (Decision Tree + Régression) + IPFS simulé
#
#  Auteurs : OULBERJ Hassane  |  HASKOUK Soufiane
#  Master SIDI — FST — Université Moulay Ismaïl — Juin 2025
#
#  Bibliothèque GUI : CustomTkinter
#  → Choix justifié : interface moderne "Material Design", thèmes dark/light,
#    widgets natifs stylisés, sans dépendance externe lourde (vs PyQt).
# =============================================================================

# ── Bibliothèques standard ───────────────────────────────────────────────────
import os, sys, time, json, random, hashlib, base64, threading, datetime, math
from collections import deque

# ── Interface graphique ──────────────────────────────────────────────────────
import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox
import customtkinter as ctk

# ── Cryptographie ECC ────────────────────────────────────────────────────────
from cryptography.hazmat.primitives.asymmetric.ec import (
    generate_private_key, SECP256K1, SECP384R1, SECP521R1,
    ECDH, EllipticCurvePublicKey
)
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.kdf.hkdf import HKDF
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.backends import default_backend

# ── Intelligence Artificielle ────────────────────────────────────────────────
import numpy as np
from sklearn.tree import DecisionTreeClassifier
from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import LabelEncoder

# ── Graphiques ───────────────────────────────────────────────────────────────
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import matplotlib.patches as mpatches

# =============================================================================
#  PALETTE & THÈME
# =============================================================================
THEME = {
    "bg_dark":     "#0D1117",
    "bg_card":     "#161B22",
    "bg_card2":    "#1C2128",
    "border":      "#30363D",
    "blue":        "#58A6FF",
    "blue_dark":   "#1F6FEB",
    "green":       "#3FB950",
    "green_dark":  "#238636",
    "orange":      "#F0883E",
    "red":         "#F85149",
    "purple":      "#BC8CFF",
    "cyan":        "#56D2E0",
    "text_prim":   "#E6EDF3",
    "text_sec":    "#8B949E",
    "text_muted":  "#484F58",
    "accent":      "#58A6FF",
    "success":     "#3FB950",
    "warning":     "#D29922",
}

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

# =============================================================================
#  MODULE 1 — GÉNÉRATION DE DONNÉES IoMT
# =============================================================================
class IoMTGenerator:
    """
    Simule des capteurs IoMT (Internet of Medical Things).
    Génère des données médicales réalistes avec profils patient.
    """

    SENSOR_PROFILES = {
        "Normal":   {"temp": (36.2, 37.2), "hr": (60, 80), "bp_s": (110, 125),
                     "bp_d": (70, 82), "spo2": (97, 100), "glucose": (80, 100)},
        "Critique": {"temp": (38.5, 40.5), "hr": (100, 145), "bp_s": (160, 190),
                     "bp_d": (95, 115), "spo2": (85, 93), "glucose": (180, 350)},
        "Anomalie": {"temp": (34.0, 35.8), "hr": (40, 55), "bp_s": (85, 100),
                     "bp_d": (50, 65), "spo2": (90, 95), "glucose": (50, 70)},
    }

    @staticmethod
    def generate(patient_id: str = None, profile: str = "Normal") -> dict:
        """Génère un paquet de données médicales simulées."""
        p = IoMTGenerator.SENSOR_PROFILES.get(profile, IoMTGenerator.SENSOR_PROFILES["Normal"])

        def rv(lo, hi, dec=1):
            return round(random.uniform(lo, hi), dec)

        if not patient_id:
            patient_id = f"PAT-{random.randint(1000, 9999)}"

        data = {
            "patient_id":     patient_id,
            "timestamp":      datetime.datetime.now().isoformat(),
            "profile":        profile,
            "temperature_C":  rv(*p["temp"]),
            "heart_rate_bpm": rv(*p["hr"], 0),
            "blood_pressure": f"{rv(*p['bp_s'],0)}/{rv(*p['bp_d'],0)}",
            "spo2_pct":       rv(*p["spo2"]),
            "glucose_mgdl":   rv(*p["glucose"], 0),
            "sensor_id":      f"SENSOR-{random.randint(100,999)}",
            "device_model":   random.choice(["MedBand Pro", "HealthNode X3",
                                              "BioSense Ultra", "VitalTrack 5G"]),
            "battery_pct":    rv(15, 100, 0),
            "signal_quality": random.choice(["Excellent", "Bon", "Faible"]),
        }
        return data

# =============================================================================
#  MODULE 2 — CRYPTOGRAPHIE ECC
# =============================================================================
class ECCCrypto:
    """
    Implémentation ECC basée sur la bibliothèque `cryptography` (Python).

    Algorithme utilisé : ECIES (Elliptic Curve Integrated Encryption Scheme)
    ─────────────────────────────────────────────────────────────────────────
    Étapes :
      1. Génération d'une paire de clés (privée k, publique Q = k·G)
      2. Génération d'une clé éphémère (r, R = r·G)
      3. Calcul du secret partagé S = ECDH(r, Q_destinataire)
      4. Dérivation d'une clé AES via HKDF(S)
      5. Chiffrement AES-256-GCM du message
      6. Envoi de (R_pub, nonce, tag, ciphertext)
    """

    CURVES = {
        "secp256k1": SECP256K1,   # Bitcoin/Ethereum — 256 bits — rapide
        "secp384r1": SECP384R1,   # NSA Suite B — 384 bits — sécurité haute
        "secp521r1": SECP521R1,   # NSA Suite B — 521 bits — sécurité max
    }

    def __init__(self, curve_name: str = "secp256k1"):
        self.curve_name = curve_name
        self.curve = self.CURVES[curve_name]()
        self.private_key = None
        self.public_key  = None
        self.backend = default_backend()

    # ── Génération de clés ───────────────────────────────────────────────────
    def generate_keys(self) -> dict:
        """
        Génère une paire de clés ECC sur la courbe choisie.
        Retourne les clés sous forme PEM + coordonnées brutes.
        """
        t0 = time.perf_counter()
        self.private_key = generate_private_key(self.curve, self.backend)
        self.public_key  = self.private_key.public_key()
        elapsed = (time.perf_counter() - t0) * 1000  # ms

        # Sérialisation PEM (format standard)
        priv_pem = self.private_key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption()
        ).decode()

        pub_pem = self.public_key.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo
        ).decode()

        # Coordonnées du point public (x, y)
        pub_nums = self.public_key.public_key().key_size \
            if hasattr(self.public_key, 'public_key') else None
        try:
            pub_nums = self.public_key.public_numbers()
            x_hex = hex(pub_nums.x)
            y_hex = hex(pub_nums.y)
        except Exception:
            x_hex = y_hex = "N/A"

        return {
            "curve":      self.curve_name,
            "key_size":   self.private_key.key_size,
            "private_pem": priv_pem,
            "public_pem":  pub_pem,
            "pub_x":       x_hex,
            "pub_y":       y_hex,
            "gen_time_ms": round(elapsed, 3),
        }

    # ── Chiffrement ECIES ────────────────────────────────────────────────────
    def encrypt(self, plaintext: str) -> dict:
        """
        Chiffre un message via ECIES :
          ECC-ECDH → Secret partagé → HKDF → AES-256-GCM
        Retourne toutes les données intermédiaires pour la visualisation.
        """
        if not self.public_key:
            raise RuntimeError("Clés non générées. Appelez generate_keys() d'abord.")

        t0 = time.perf_counter()
        steps = []

        # Étape 1 : clé éphémère
        steps.append("⚙️  Génération clé éphémère (r, R=r·G)...")
        ephemeral_key = generate_private_key(self.curve, self.backend)
        ephemeral_pub = ephemeral_key.public_key()

        # Étape 2 : ECDH — secret partagé
        steps.append("🔗 Calcul secret partagé ECDH : S = r · Q_destinataire")
        shared_secret = ephemeral_key.exchange(ECDH(), self.public_key)

        # Étape 3 : dérivation de clé AES via HKDF
        steps.append("🔑 Dérivation clé AES-256 via HKDF-SHA256...")
        hkdf = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=None,
            info=b"IoMT-ECC-v1",
            backend=self.backend
        )
        aes_key = hkdf.derive(shared_secret)

        # Étape 4 : chiffrement AES-256-GCM
        steps.append("🔒 Chiffrement AES-256-GCM du message...")
        nonce = os.urandom(12)
        encryptor = Cipher(
            algorithms.AES(aes_key),
            modes.GCM(nonce),
            backend=self.backend
        ).encryptor()

        pt_bytes = plaintext.encode("utf-8")
        ciphertext = encryptor.update(pt_bytes) + encryptor.finalize()
        tag = encryptor.tag

        # Étape 5 : sérialisation de la clé éphémère publique
        steps.append("📦 Assemblage du paquet chiffré (R, nonce, tag, ciphertext)...")
        eph_pub_bytes = ephemeral_pub.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo
        )

        elapsed = (time.perf_counter() - t0) * 1000

        return {
            "plaintext":        plaintext,
            "plaintext_b64":    base64.b64encode(pt_bytes).decode(),
            "ephemeral_pub_pem": eph_pub_bytes.decode(),
            "shared_secret_hex": shared_secret.hex(),
            "aes_key_hex":      aes_key.hex(),
            "nonce_hex":        nonce.hex(),
            "tag_hex":          tag.hex(),
            "ciphertext_b64":   base64.b64encode(ciphertext).decode(),
            "ciphertext_hex":   ciphertext.hex(),
            "steps":            steps,
            "enc_time_ms":      round(elapsed, 3),
            "plaintext_len":    len(pt_bytes),
            "ciphertext_len":   len(ciphertext),
            "_raw": {
                "eph_key": ephemeral_key,
                "nonce":   nonce,
                "tag":     tag,
                "ct":      ciphertext,
            }
        }

    # ── Déchiffrement ECIES ──────────────────────────────────────────────────
    def decrypt(self, enc_result: dict) -> dict:
        """
        Déchiffre un paquet ECIES avec la clé privée du destinataire.
        """
        if not self.private_key:
            raise RuntimeError("Clé privée non disponible.")

        t0 = time.perf_counter()
        raw = enc_result["_raw"]

        # Recalcul du secret partagé côté destinataire
        shared_secret = self.private_key.exchange(
            ECDH(), raw["eph_key"].public_key()
        )

        # Re-dérivation de la clé AES
        hkdf = HKDF(
            algorithm=hashes.SHA256(),
            length=32,
            salt=None,
            info=b"IoMT-ECC-v1",
            backend=self.backend
        )
        aes_key = hkdf.derive(shared_secret)

        # Déchiffrement AES-GCM
        decryptor = Cipher(
            algorithms.AES(aes_key),
            modes.GCM(raw["nonce"], raw["tag"]),
            backend=self.backend
        ).decryptor()

        plaintext = (decryptor.update(raw["ct"]) + decryptor.finalize()).decode("utf-8")
        elapsed = (time.perf_counter() - t0) * 1000

        return {
            "decrypted_text": plaintext,
            "dec_time_ms":    round(elapsed, 3),
            "verified":       (plaintext == enc_result["plaintext"]),
        }

# =============================================================================
#  MODULE 3 — INTELLIGENCE ARTIFICIELLE
# =============================================================================
class AIOptimizer:
    """
    Module IA dual :
      1. DecisionTree → Classification de la courbe ECC optimale
         selon le profil de données (taille, criticité, batterie)
      2. LinearRegression → Prédiction du temps de chiffrement
         selon la taille du message et la courbe
    """

    def __init__(self):
        self.dt_model  = None   # Classificateur de courbe
        self.lr_model  = None   # Régresseur temps de chiffrement
        self.le_curve  = LabelEncoder()
        self.le_profile = LabelEncoder()
        self.trained   = False
        self.history   = []     # Historique des métriques

    # ── Entraînement ────────────────────────────────────────────────────────
    def train(self):
        """
        Génère un jeu de données synthétique et entraîne les deux modèles.

        Features (X) :
          - data_size    : taille du message en octets
          - criticality  : niveau critique (0=Normal, 1=Anomalie, 2=Critique)
          - battery_pct  : niveau de batterie du capteur (0-100)
          - signal_qual  : qualité signal (0=Faible, 1=Bon, 2=Excellent)

        Cibles :
          - DT  → curve_name (secp256k1 / secp384r1 / secp521r1)
          - LR  → enc_time_ms (prédiction numérique)
        """
        np.random.seed(42)
        N = 500

        # Génération de données d'entraînement synthétiques
        data_size    = np.random.randint(100, 2000, N)
        criticality  = np.random.randint(0, 3, N)
        battery_pct  = np.random.randint(10, 100, N)
        signal_qual  = np.random.randint(0, 3, N)

        X = np.column_stack([data_size, criticality, battery_pct, signal_qual])

        # Règle de décision pour la courbe (logique métier encodée)
        # Critique + petite batterie → courbe forte (521)
        # Critique + bonne batterie  → courbe intermédiaire (384)
        # Normal                     → courbe rapide (256k1)
        y_curve_labels = []
        for i in range(N):
            if criticality[i] == 2:
                if battery_pct[i] < 30:
                    y_curve_labels.append("secp384r1")
                else:
                    y_curve_labels.append("secp521r1")
            elif criticality[i] == 1:
                y_curve_labels.append("secp384r1")
            else:
                y_curve_labels.append("secp256k1")

        y_curve = self.le_curve.fit_transform(y_curve_labels)

        # Temps de chiffrement simulé : modèle linéaire + bruit
        # (basé sur des mesures réelles approximatives)
        curve_factor = np.array([
            0.08 if c == "secp256k1" else
            0.15 if c == "secp384r1" else 0.25
            for c in y_curve_labels
        ])
        y_time = data_size * curve_factor + np.random.normal(0, 0.5, N)
        y_time = np.clip(y_time, 0.1, 500)

        # Entraînement
        self.dt_model = DecisionTreeClassifier(max_depth=5, random_state=42)
        self.dt_model.fit(X, y_curve)

        self.lr_model = LinearRegression()
        self.lr_model.fit(
            np.column_stack([data_size, curve_factor]),
            y_time
        )

        self.trained = True
        return {"status": "ok", "n_samples": N}

    # ── Prédiction ────────────────────────────────────────────────────────
    def recommend(self, data_size: int, profile: str,
                  battery_pct: float, signal_qual: str) -> dict:
        """
        Recommande la courbe ECC optimale et prédit le temps de chiffrement.
        """
        if not self.trained:
            self.train()

        criticality = {"Normal": 0, "Anomalie": 1, "Critique": 2}.get(profile, 0)
        sig_num     = {"Faible": 0, "Bon": 1, "Excellent": 2}.get(signal_qual, 1)

        X = np.array([[data_size, criticality, battery_pct, sig_num]])
        curve_idx = self.dt_model.predict(X)[0]
        curve_name = self.le_curve.inverse_transform([curve_idx])[0]

        curve_factor = {"secp256k1": 0.08, "secp384r1": 0.15, "secp521r1": 0.25}
        pred_time = float(self.lr_model.predict(
            np.array([[data_size, curve_factor[curve_name]]])
        )[0])

        # Confiance du DT (probabilité de la classe prédite)
        confidence = float(self.dt_model.predict_proba(X)[0].max()) * 100

        result = {
            "recommended_curve": curve_name,
            "predicted_time_ms": round(max(pred_time, 0.1), 2),
            "confidence_pct":    round(confidence, 1),
            "data_size":         data_size,
            "profile":           profile,
            "battery_pct":       battery_pct,
            "reasoning": self._explain(curve_name, profile, battery_pct),
        }
        self.history.append(result)
        return result

    def _explain(self, curve: str, profile: str, battery: float) -> str:
        reasons = {
            "secp256k1": f"Profil '{profile}' peu critique → courbe rapide 256-bit (↓ énergie)",
            "secp384r1": f"Profil '{profile}' + batterie {battery:.0f}% → équilibre sécurité/perf",
            "secp521r1": f"Profil CRITIQUE + ressources suffisantes → sécurité maximale 521-bit",
        }
        return reasons.get(curve, "Recommandation basée sur les données d'entraînement")

# =============================================================================
#  MODULE 4 — SIMULATION IPFS
# =============================================================================
class IPFSSimulator:
    """
    Simule un nœud IPFS local avec stockage en mémoire.
    Génère des CID (Content Identifiers) réalistes.
    Les CID IPFS réels sont des hashes SHA-256 encodés en Base58.
    """

    BASE58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    store = {}  # Stockage en mémoire (simulé)

    @classmethod
    def _bytes_to_base58(cls, data: bytes) -> str:
        """Encodage Base58 (comme Bitcoin/IPFS)."""
        count = 0
        for byte in data:
            if byte == 0:
                count += 1
            else:
                break
        num = int.from_bytes(data, "big")
        result = ""
        while num > 0:
            num, remainder = divmod(num, 58)
            result = cls.BASE58_ALPHABET[remainder] + result
        return "1" * count + result

    @classmethod
    def add(cls, data: str, filename: str = "iomt_data.enc") -> dict:
        """
        Ajoute des données chiffrées à l'IPFS simulé.
        Retourne un CID v0 simulé (format Qm...).
        """
        t0 = time.perf_counter()
        content = data.encode("utf-8")

        # Hash SHA-256 du contenu
        sha256 = hashlib.sha256(content).digest()

        # Simulation CID v0 : préfixe multihash (0x1220) + hash SHA256
        multihash = bytes([0x12, 0x20]) + sha256
        cid = "Qm" + cls._bytes_to_base58(multihash)[:44]

        # Stockage en mémoire
        cls.store[cid] = {
            "content":   data,
            "filename":  filename,
            "size_bytes": len(content),
            "timestamp": datetime.datetime.now().isoformat(),
            "sha256":    sha256.hex(),
            "pinned":    True,
        }

        elapsed = (time.perf_counter() - t0) * 1000
        return {
            "cid":          cid,
            "size_bytes":   len(content),
            "sha256":       sha256.hex(),
            "pin_status":   "pinned",
            "store_time_ms": round(elapsed, 3),
            "gateway_url":  f"https://ipfs.io/ipfs/{cid}",
        }

    @classmethod
    def get(cls, cid: str) -> dict | None:
        """Récupère des données depuis l'IPFS simulé."""
        return cls.store.get(cid)

# =============================================================================
#  MODULE 5 — COMPARAISON ECC vs RSA
# =============================================================================
class RSABenchmark:
    """Implémente un chiffrement RSA simplifié pour comparaison avec ECC."""

    @staticmethod
    def benchmark(key_sizes=(1024, 2048, 3072)) -> list:
        from cryptography.hazmat.primitives.asymmetric import rsa, padding
        results = []
        for ks in key_sizes:
            try:
                # Génération clé RSA
                t0 = time.perf_counter()
                priv = rsa.generate_private_key(
                    public_exponent=65537, key_size=ks,
                    backend=default_backend()
                )
                keygen_t = (time.perf_counter() - t0) * 1000

                # Chiffrement RSA-OAEP
                msg = b"IoMT sensor data benchmark test payload" * 3
                pub = priv.public_key()
                t1 = time.perf_counter()
                ct = pub.encrypt(msg[:190], padding.OAEP(
                    mgf=padding.MGF1(hashes.SHA256()),
                    algorithm=hashes.SHA256(), label=None
                ))
                enc_t = (time.perf_counter() - t1) * 1000

                results.append({
                    "key_size": ks,
                    "keygen_ms": round(keygen_t, 2),
                    "enc_ms":   round(enc_t, 2),
                })
            except Exception as e:
                results.append({"key_size": ks, "error": str(e)})
        return results

# =============================================================================
#  INTERFACE GRAPHIQUE — APPLICATION PRINCIPALE
# =============================================================================
class IoMTApp(ctk.CTk):
    """
    Application principale CustomTkinter.
    Organise l'interface en onglets thématiques.
    """

    def __init__(self):
        super().__init__()

        # ── Fenêtre ──────────────────────────────────────────────────────
        self.title("🔐 IoMT-ECC Secure System  |  Master SIDI — UMI")
        self.geometry("1280x820")
        self.minsize(1100, 700)
        self.configure(fg_color=THEME["bg_dark"])

        # ── État partagé ──────────────────────────────────────────────────
        self.iomt_data    = None
        self.ecc          = ECCCrypto()
        self.key_info     = None
        self.enc_result   = None
        self.dec_result   = None
        self.ai_optimizer = AIOptimizer()
        self.ai_result    = None
        self.ipfs_result  = None
        self.perf_history = deque(maxlen=30)  # Historique perf pour graphiques
        self.log_lines    = []

        # ── Construction UI ───────────────────────────────────────────────
        self._build_header()
        self._build_tabs()
        self._build_statusbar()

        # Entraîner le modèle IA en arrière-plan
        threading.Thread(target=self._init_ai, daemon=True).start()

    # =========================================================================
    #  EN-TÊTE
    # =========================================================================
    def _build_header(self):
        hdr = ctk.CTkFrame(self, fg_color=THEME["bg_card"], height=60,
                           corner_radius=0)
        hdr.pack(fill="x", side="top")
        hdr.pack_propagate(False)

        # Logo / titre
        ctk.CTkLabel(
            hdr,
            text="🔐  IoMT-ECC Secure System",
            font=ctk.CTkFont("Courier New", 20, "bold"),
            text_color=THEME["blue"],
        ).pack(side="left", padx=20, pady=12)

        ctk.CTkLabel(
            hdr,
            text="Cryptographie ECC · IA · IPFS · IoMT",
            font=ctk.CTkFont("Courier New", 11),
            text_color=THEME["text_sec"],
        ).pack(side="left", padx=0, pady=12)

        # Bouton simulation complète
        ctk.CTkButton(
            hdr, text="▶  Simulation Complète",
            font=ctk.CTkFont(size=12, weight="bold"),
            fg_color=THEME["green_dark"], hover_color=THEME["green"],
            width=180, height=36, corner_radius=8,
            command=self._run_full_simulation,
        ).pack(side="right", padx=12, pady=12)

        # Sélecteur de thème
        ctk.CTkButton(
            hdr, text="🌙", width=36, height=36, corner_radius=18,
            fg_color=THEME["bg_card2"], hover_color=THEME["border"],
            command=self._toggle_theme,
        ).pack(side="right", padx=4, pady=12)

    # =========================================================================
    #  ONGLETS
    # =========================================================================
    def _build_tabs(self):
        self.tabview = ctk.CTkTabview(
            self,
            fg_color=THEME["bg_card"],
            segmented_button_fg_color=THEME["bg_card2"],
            segmented_button_selected_color=THEME["blue_dark"],
            segmented_button_selected_hover_color=THEME["blue"],
            segmented_button_unselected_color=THEME["bg_card2"],
            segmented_button_unselected_hover_color=THEME["border"],
            text_color=THEME["text_prim"],
            text_color_disabled=THEME["text_muted"],
        )
        self.tabview.pack(fill="both", expand=True, padx=8, pady=(4, 0))

        tabs = [
            ("📊 Capteurs IoMT",   self._build_tab_iomt),
            ("🔐 Chiffrement ECC", self._build_tab_encrypt),
            ("🔓 Déchiffrement",   self._build_tab_decrypt),
            ("🤖 Module IA",       self._build_tab_ai),
            ("📦 IPFS",            self._build_tab_ipfs),
            ("📈 Performances",    self._build_tab_perf),
            ("📋 Logs",            self._build_tab_logs),
        ]

        for name, builder in tabs:
            self.tabview.add(name)
            builder(self.tabview.tab(name))

    # =========================================================================
    #  ONGLET 1 — CAPTEURS IoMT
    # =========================================================================
    def _build_tab_iomt(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        # ── Panneau de contrôle ───────────────────────────────────────────
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="⚙️  Paramètres du capteur",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["blue"]).pack(anchor="w", padx=16, pady=(10,4))

        row = ctk.CTkFrame(ctrl, fg_color="transparent")
        row.pack(fill="x", padx=16, pady=(0,10))

        ctk.CTkLabel(row, text="Patient ID :", text_color=THEME["text_sec"],
                     width=90).grid(row=0, column=0, padx=4, pady=4, sticky="w")
        self.patient_id_var = ctk.StringVar(value="PAT-4271")
        ctk.CTkEntry(row, textvariable=self.patient_id_var, width=120).grid(
            row=0, column=1, padx=4, pady=4)

        ctk.CTkLabel(row, text="Profil :", text_color=THEME["text_sec"],
                     width=60).grid(row=0, column=2, padx=4, pady=4, sticky="w")
        self.profile_var = ctk.StringVar(value="Normal")
        ctk.CTkOptionMenu(row, variable=self.profile_var,
                          values=["Normal", "Critique", "Anomalie"],
                          fg_color=THEME["bg_card2"],
                          button_color=THEME["blue_dark"],
                          width=120).grid(row=0, column=3, padx=4, pady=4)

        ctk.CTkButton(row, text="🔄  Générer données",
                      fg_color=THEME["blue_dark"], hover_color=THEME["blue"],
                      width=160, command=self._generate_iomt_data
                      ).grid(row=0, column=4, padx=12, pady=4)

        # ── Affichage des données ─────────────────────────────────────────
        display_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"],
                                     corner_radius=10)
        display_frame.pack(fill="both", expand=True, padx=10, pady=(0,8))

        ctk.CTkLabel(display_frame, text="📊  Données générées",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["green"]).pack(anchor="w", padx=16, pady=(10,4))

        # Grille de métriques visuelles
        self.metrics_frame = ctk.CTkFrame(display_frame, fg_color="transparent")
        self.metrics_frame.pack(fill="x", padx=16, pady=4)

        self.metric_labels = {}
        sensors = [
            ("🌡️", "Température",  "temperature_C",  "°C"),
            ("❤️", "Rythme Card.", "heart_rate_bpm", "bpm"),
            ("🩺", "Pression",     "blood_pressure", "mmHg"),
            ("💧", "SpO₂",         "spo2_pct",        "%"),
            ("🍬", "Glucose",      "glucose_mgdl",    "mg/dL"),
            ("🔋", "Batterie",     "battery_pct",     "%"),
        ]
        for i, (emoji, label, key, unit) in enumerate(sensors):
            card = ctk.CTkFrame(self.metrics_frame, fg_color=THEME["bg_card2"],
                                corner_radius=8, width=160, height=80)
            card.grid(row=0, column=i, padx=6, pady=4, sticky="nsew")
            card.grid_propagate(False)
            self.metrics_frame.columnconfigure(i, weight=1)

            ctk.CTkLabel(card, text=f"{emoji} {label}",
                         font=ctk.CTkFont(size=10),
                         text_color=THEME["text_sec"]).place(x=8, y=8)
            val_lbl = ctk.CTkLabel(card, text="--",
                                   font=ctk.CTkFont("Courier New", 18, "bold"),
                                   text_color=THEME["cyan"])
            val_lbl.place(x=8, y=30)
            ctk.CTkLabel(card, text=unit, font=ctk.CTkFont(size=9),
                         text_color=THEME["text_muted"]).place(x=8, y=58)
            self.metric_labels[key] = val_lbl

        # JSON brut
        ctk.CTkLabel(display_frame, text="📄  JSON brut (avant chiffrement)",
                     font=ctk.CTkFont(size=11),
                     text_color=THEME["text_sec"]).pack(anchor="w", padx=16, pady=(10,2))
        self.iomt_text = ctk.CTkTextbox(display_frame, height=160,
                                         fg_color=THEME["bg_dark"],
                                         text_color=THEME["text_prim"],
                                         font=ctk.CTkFont("Courier New", 11),
                                         corner_radius=6)
        self.iomt_text.pack(fill="both", expand=True, padx=16, pady=(0,12))

    # =========================================================================
    #  ONGLET 2 — CHIFFREMENT ECC
    # =========================================================================
    def _build_tab_encrypt(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        # ── Contrôles ─────────────────────────────────────────────────────
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="🔐  Paramètres ECC",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["blue"]).pack(anchor="w", padx=16, pady=(10,4))

        row = ctk.CTkFrame(ctrl, fg_color="transparent")
        row.pack(fill="x", padx=16, pady=(0,10))

        ctk.CTkLabel(row, text="Courbe :", text_color=THEME["text_sec"]).grid(
            row=0, column=0, padx=4, pady=4, sticky="w")
        self.curve_var = ctk.StringVar(value="secp256k1")
        ctk.CTkOptionMenu(row, variable=self.curve_var,
                          values=["secp256k1", "secp384r1", "secp521r1"],
                          fg_color=THEME["bg_card2"],
                          button_color=THEME["blue_dark"],
                          width=130).grid(row=0, column=1, padx=4, pady=4)

        ctk.CTkButton(row, text="🗝️  Générer clés",
                      fg_color=THEME["orange"], hover_color="#ffaa55",
                      text_color="#000", width=140,
                      command=self._generate_keys
                      ).grid(row=0, column=2, padx=8, pady=4)

        ctk.CTkButton(row, text="🔒  Chiffrer données",
                      fg_color=THEME["blue_dark"], hover_color=THEME["blue"],
                      width=150, command=self._encrypt_data
                      ).grid(row=0, column=3, padx=4, pady=4)

        # ── Affichage clés + résultats ────────────────────────────────────
        pane = ctk.CTkFrame(parent, fg_color="transparent")
        pane.pack(fill="both", expand=True, padx=10, pady=(0,8))
        pane.columnconfigure(0, weight=1)
        pane.columnconfigure(1, weight=1)
        pane.rowconfigure(0, weight=1)

        # Colonne gauche — Clés ECC
        left = ctk.CTkFrame(pane, fg_color=THEME["bg_card"], corner_radius=10)
        left.grid(row=0, column=0, padx=(0,4), pady=0, sticky="nsew")

        ctk.CTkLabel(left, text="🗝️  Clés ECC générées",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["orange"]).pack(anchor="w", padx=12, pady=(10,4))

        # Mini cartes d'info clé
        self.key_info_frame = ctk.CTkFrame(left, fg_color="transparent")
        self.key_info_frame.pack(fill="x", padx=12, pady=4)

        self.key_badges = {}
        for badge_key, label in [("curve","Courbe"),("key_size","Taille"),
                                  ("gen_time_ms","Temps gén.")]:
            b = ctk.CTkFrame(self.key_info_frame, fg_color=THEME["bg_card2"],
                             corner_radius=6)
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=label, font=ctk.CTkFont(size=9),
                         text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            val = ctk.CTkLabel(b, text="--",
                               font=ctk.CTkFont("Courier New", 12, "bold"),
                               text_color=THEME["cyan"])
            val.pack(padx=8, pady=(0,4))
            self.key_badges[badge_key] = val

        ctk.CTkLabel(left, text="Clé publique (PEM) :",
                     font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]
                     ).pack(anchor="w", padx=12, pady=(6,2))
        self.pub_key_text = ctk.CTkTextbox(left, height=120,
                                            fg_color=THEME["bg_dark"],
                                            text_color=THEME["green"],
                                            font=ctk.CTkFont("Courier New", 9),
                                            corner_radius=6)
        self.pub_key_text.pack(fill="x", padx=12, pady=(0,4))

        ctk.CTkLabel(left, text="Clé privée (PEM) [⚠️ secrète] :",
                     font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]
                     ).pack(anchor="w", padx=12, pady=(4,2))
        self.priv_key_text = ctk.CTkTextbox(left, height=120,
                                             fg_color=THEME["bg_dark"],
                                             text_color=THEME["red"],
                                             font=ctk.CTkFont("Courier New", 9),
                                             corner_radius=6)
        self.priv_key_text.pack(fill="x", padx=12, pady=(0,8))

        # Colonne droite — Résultat chiffrement
        right = ctk.CTkFrame(pane, fg_color=THEME["bg_card"], corner_radius=10)
        right.grid(row=0, column=1, padx=(4,0), pady=0, sticky="nsew")

        ctk.CTkLabel(right, text="🔒  Résultat du chiffrement",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["blue"]).pack(anchor="w", padx=12, pady=(10,4))

        # Étapes de chiffrement
        ctk.CTkLabel(right, text="Étapes du processus :",
                     font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]
                     ).pack(anchor="w", padx=12, pady=(0,2))
        self.steps_text = ctk.CTkTextbox(right, height=90,
                                          fg_color=THEME["bg_dark"],
                                          text_color=THEME["purple"],
                                          font=ctk.CTkFont("Courier New", 10),
                                          corner_radius=6)
        self.steps_text.pack(fill="x", padx=12, pady=(0,4))

        # Métriques chiffrement
        met_row = ctk.CTkFrame(right, fg_color="transparent")
        met_row.pack(fill="x", padx=12, pady=4)
        self.enc_badges = {}
        for bk, lbl in [("enc_time_ms","Temps (ms)"),
                         ("plaintext_len","Taille claire"),
                         ("ciphertext_len","Taille chiffrée")]:
            b = ctk.CTkFrame(met_row, fg_color=THEME["bg_card2"], corner_radius=6)
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=lbl, font=ctk.CTkFont(size=9),
                         text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            v = ctk.CTkLabel(b, text="--",
                             font=ctk.CTkFont("Courier New", 12, "bold"),
                             text_color=THEME["orange"])
            v.pack(padx=8, pady=(0,4))
            self.enc_badges[bk] = v

        ctk.CTkLabel(right, text="Ciphertext (Base64) :",
                     font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]
                     ).pack(anchor="w", padx=12, pady=(4,2))
        self.cipher_text = ctk.CTkTextbox(right, height=80,
                                           fg_color=THEME["bg_dark"],
                                           text_color=THEME["orange"],
                                           font=ctk.CTkFont("Courier New", 9),
                                           corner_radius=6)
        self.cipher_text.pack(fill="x", padx=12, pady=(0,4))

        ctk.CTkLabel(right, text="Détails cryptographiques :",
                     font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]
                     ).pack(anchor="w", padx=12, pady=(4,2))
        self.enc_details_text = ctk.CTkTextbox(right, height=100,
                                                fg_color=THEME["bg_dark"],
                                                text_color=THEME["text_prim"],
                                                font=ctk.CTkFont("Courier New", 9),
                                                corner_radius=6)
        self.enc_details_text.pack(fill="both", expand=True, padx=12, pady=(0,8))

    # =========================================================================
    #  ONGLET 3 — DÉCHIFFREMENT
    # =========================================================================
    def _build_tab_decrypt(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="🔓  Déchiffrement ECIES",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["green"]).pack(side="left", padx=16, pady=12)

        ctk.CTkButton(ctrl, text="🔓  Déchiffrer",
                      fg_color=THEME["green_dark"], hover_color=THEME["green"],
                      width=140, command=self._decrypt_data
                      ).pack(side="right", padx=12, pady=8)

        # Schéma du processus de déchiffrement
        schema_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"],
                                     corner_radius=10)
        schema_frame.pack(fill="x", padx=10, pady=(0,6))
        ctk.CTkLabel(schema_frame, text="🔄  Processus de déchiffrement ECIES",
                     font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=THEME["cyan"]).pack(anchor="w", padx=16, pady=(8,4))

        steps_canvas = ctk.CTkFrame(schema_frame, fg_color="transparent", height=70)
        steps_canvas.pack(fill="x", padx=16, pady=(0,8))
        steps_canvas.pack_propagate(False)

        dec_steps = [
            ("📦 Paquet\nreçu", THEME["blue_dark"]),
            ("🔑 ECDH\nsecret", THEME["orange"]),
            ("🔑 HKDF\nclé AES", THEME["purple"]),
            ("🔓 AES-GCM\ndéchiff.", THEME["green_dark"]),
            ("✅ Message\noriginal", THEME["green"]),
        ]
        for i, (txt, color) in enumerate(dec_steps):
            b = ctk.CTkFrame(steps_canvas, fg_color=color, corner_radius=8,
                             width=120, height=56)
            b.place(x=i*148 + 10, y=7)
            ctk.CTkLabel(b, text=txt, font=ctk.CTkFont("Courier New", 10),
                         text_color="white", justify="center").place(
                relx=0.5, rely=0.5, anchor="center")
            if i < len(dec_steps)-1:
                ctk.CTkLabel(steps_canvas, text="→",
                             font=ctk.CTkFont(size=20, weight="bold"),
                             text_color=THEME["text_sec"]).place(x=i*148+132, y=18)

        # Résultat
        result_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"],
                                     corner_radius=10)
        result_frame.pack(fill="both", expand=True, padx=10, pady=(0,8))

        ctk.CTkLabel(result_frame, text="📄  Données déchiffrées",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["green"]).pack(anchor="w", padx=16, pady=(10,4))

        # Badge de vérification
        self.verify_badge = ctk.CTkLabel(
            result_frame, text="⏳ En attente...",
            font=ctk.CTkFont(size=12, weight="bold"),
            fg_color=THEME["bg_card2"], corner_radius=8,
            text_color=THEME["text_sec"],
            padx=12, pady=6
        )
        self.verify_badge.pack(anchor="w", padx=16, pady=4)

        # Métriques déchiffrement
        met_row = ctk.CTkFrame(result_frame, fg_color="transparent")
        met_row.pack(fill="x", padx=16, pady=4)
        self.dec_badges = {}
        for bk, lbl in [("dec_time_ms","Temps déchiff. (ms)"),
                         ("verified","Intégrité vérifiée")]:
            b = ctk.CTkFrame(met_row, fg_color=THEME["bg_card2"], corner_radius=6)
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=lbl, font=ctk.CTkFont(size=9),
                         text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            v = ctk.CTkLabel(b, text="--",
                             font=ctk.CTkFont("Courier New", 12, "bold"),
                             text_color=THEME["green"])
            v.pack(padx=8, pady=(0,4))
            self.dec_badges[bk] = v

        self.dec_text = ctk.CTkTextbox(result_frame,
                                        fg_color=THEME["bg_dark"],
                                        text_color=THEME["green"],
                                        font=ctk.CTkFont("Courier New", 11),
                                        corner_radius=6)
        self.dec_text.pack(fill="both", expand=True, padx=16, pady=(4,12))

    # =========================================================================
    #  ONGLET 4 — MODULE IA
    # =========================================================================
    def _build_tab_ai(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="🤖  Optimisation par Intelligence Artificielle",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["purple"]).pack(side="left", padx=16, pady=12)

        ctk.CTkButton(ctrl, text="🧠  Analyser & Recommander",
                      fg_color="#5e35b1", hover_color=THEME["purple"],
                      width=200, command=self._run_ai_analysis
                      ).pack(side="right", padx=12, pady=8)

        pane = ctk.CTkFrame(parent, fg_color="transparent")
        pane.pack(fill="both", expand=True, padx=10, pady=(0,8))
        pane.columnconfigure(0, weight=1)
        pane.columnconfigure(1, weight=2)
        pane.rowconfigure(0, weight=1)

        # Colonne gauche — Description IA
        left = ctk.CTkFrame(pane, fg_color=THEME["bg_card"], corner_radius=10)
        left.grid(row=0, column=0, padx=(0,4), pady=0, sticky="nsew")

        ctk.CTkLabel(left, text="📐  Architecture IA",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["purple"]).pack(anchor="w", padx=12, pady=(10,4))

        arch_info = [
            ("Modèle 1", "Decision Tree", "Classification courbe optimale"),
            ("Modèle 2", "LinearRegression", "Prédiction temps chiffrement"),
            ("Features", "4 entrées", "taille, criticité, batterie, signal"),
            ("Labels DT", "3 courbes", "secp256k1 / 384r1 / 521r1"),
            ("Dataset", "500 échantillons", "synthétiques + règles métier"),
        ]
        for title, value, desc in arch_info:
            row = ctk.CTkFrame(left, fg_color=THEME["bg_card2"], corner_radius=6)
            row.pack(fill="x", padx=12, pady=3)
            ctk.CTkLabel(row, text=title, font=ctk.CTkFont(size=9),
                         text_color=THEME["text_sec"], width=70).pack(side="left", padx=8, pady=6)
            ctk.CTkLabel(row, text=value,
                         font=ctk.CTkFont("Courier New", 11, "bold"),
                         text_color=THEME["purple"]).pack(side="left", padx=4)
            ctk.CTkLabel(row, text=f"— {desc}", font=ctk.CTkFont(size=9),
                         text_color=THEME["text_muted"]).pack(side="left", padx=4)

        ctk.CTkLabel(left, text="🎯  Résultat de l'analyse",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["cyan"]).pack(anchor="w", padx=12, pady=(14,4))

        self.ai_result_text = ctk.CTkTextbox(left, fg_color=THEME["bg_dark"],
                                              text_color=THEME["text_prim"],
                                              font=ctk.CTkFont("Courier New", 10),
                                              corner_radius=6)
        self.ai_result_text.pack(fill="both", expand=True, padx=12, pady=(0,10))

        # Colonne droite — Graphique IA
        right = ctk.CTkFrame(pane, fg_color=THEME["bg_card"], corner_radius=10)
        right.grid(row=0, column=1, padx=(4,0), pady=0, sticky="nsew")

        ctk.CTkLabel(right, text="📊  Visualisation — Espace de décision",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["cyan"]).pack(anchor="w", padx=12, pady=(10,4))

        self.ai_fig = Figure(figsize=(6, 4.2),
                             facecolor=THEME["bg_card"],
                             tight_layout=True)
        self.ai_canvas = FigureCanvasTkAgg(self.ai_fig, master=right)
        self.ai_canvas.get_tk_widget().pack(fill="both", expand=True, padx=8, pady=(0,8))
        self._draw_ai_placeholder()

    # =========================================================================
    #  ONGLET 5 — IPFS
    # =========================================================================
    def _build_tab_ipfs(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="📦  Simulation IPFS (InterPlanetary File System)",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["cyan"]).pack(side="left", padx=16, pady=12)

        ctk.CTkButton(ctrl, text="📤  Publier sur IPFS",
                      fg_color="#00695c", hover_color=THEME["cyan"],
                      text_color="white", width=160,
                      command=self._publish_ipfs
                      ).pack(side="right", padx=12, pady=8)

        # Info CID
        cid_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        cid_frame.pack(fill="x", padx=10, pady=(0,6))

        ctk.CTkLabel(cid_frame, text="🔗  Content Identifier (CID)",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["cyan"]).pack(anchor="w", padx=16, pady=(10,4))

        self.cid_label = ctk.CTkLabel(
            cid_frame,
            text="En attente de publication...",
            font=ctk.CTkFont("Courier New", 14, "bold"),
            text_color=THEME["cyan"],
            fg_color=THEME["bg_dark"],
            corner_radius=6,
            padx=12, pady=8
        )
        self.cid_label.pack(fill="x", padx=16, pady=4)

        # Détails
        details_frame = ctk.CTkFrame(cid_frame, fg_color="transparent")
        details_frame.pack(fill="x", padx=16, pady=(0,10))
        self.ipfs_badges = {}
        for bk, lbl in [("size_bytes","Taille"), ("sha256","SHA-256 (tronqué)"),
                         ("pin_status","Statut"), ("store_time_ms","Temps (ms)")]:
            b = ctk.CTkFrame(details_frame, fg_color=THEME["bg_card2"], corner_radius=6)
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=lbl, font=ctk.CTkFont(size=9),
                         text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            v = ctk.CTkLabel(b, text="--",
                             font=ctk.CTkFont("Courier New", 11, "bold"),
                             text_color=THEME["cyan"])
            v.pack(padx=8, pady=(0,4))
            self.ipfs_badges[bk] = v

        # Nœuds IPFS simulés
        nodes_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        nodes_frame.pack(fill="both", expand=True, padx=10, pady=(0,8))
        ctk.CTkLabel(nodes_frame, text="🌐  Réseau IPFS simulé — Nœuds actifs",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["cyan"]).pack(anchor="w", padx=16, pady=(10,4))

        self.ipfs_fig = Figure(figsize=(8, 3),
                               facecolor=THEME["bg_card"],
                               tight_layout=True)
        self.ipfs_canvas = FigureCanvasTkAgg(self.ipfs_fig, master=nodes_frame)
        self.ipfs_canvas.get_tk_widget().pack(fill="both", expand=True, padx=8, pady=(0,8))
        self._draw_ipfs_network()

        self.ipfs_detail_text = ctk.CTkTextbox(
            nodes_frame, height=80,
            fg_color=THEME["bg_dark"],
            text_color=THEME["text_prim"],
            font=ctk.CTkFont("Courier New", 10),
            corner_radius=6
        )
        self.ipfs_detail_text.pack(fill="x", padx=16, pady=(0,12))

    # =========================================================================
    #  ONGLET 6 — PERFORMANCES
    # =========================================================================
    def _build_tab_perf(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(ctrl, text="📈  Analyse de performance — ECC vs RSA",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["orange"]).pack(side="left", padx=16, pady=12)
        ctk.CTkButton(ctrl, text="🔬  Lancer benchmark",
                      fg_color="#b45309", hover_color=THEME["orange"],
                      text_color="white", width=160,
                      command=self._run_benchmark
                      ).pack(side="right", padx=12, pady=8)

        self.perf_fig = Figure(figsize=(10, 4.8),
                               facecolor=THEME["bg_dark"],
                               tight_layout=True)
        self.perf_canvas = FigureCanvasTkAgg(self.perf_fig, master=parent)
        self.perf_canvas.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=(0,8))
        self._draw_perf_placeholder()

    # =========================================================================
    #  ONGLET 7 — LOGS
    # =========================================================================
    def _build_tab_logs(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10)
        ctrl.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(ctrl, text="📋  Journal d'événements temps réel",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["text_prim"]).pack(side="left", padx=16, pady=10)
        ctk.CTkButton(ctrl, text="🗑️  Effacer",
                      fg_color=THEME["bg_card2"], hover_color=THEME["border"],
                      width=100, command=self._clear_logs
                      ).pack(side="right", padx=8, pady=8)

        self.log_text = ctk.CTkTextbox(
            parent,
            fg_color=THEME["bg_dark"],
            text_color=THEME["text_prim"],
            font=ctk.CTkFont("Courier New", 10),
            corner_radius=6
        )
        self.log_text.pack(fill="both", expand=True, padx=10, pady=(0,8))

    # =========================================================================
    #  BARRE D'ÉTAT
    # =========================================================================
    def _build_statusbar(self):
        self.statusbar = ctk.CTkFrame(self, fg_color=THEME["bg_card"],
                                      height=28, corner_radius=0)
        self.statusbar.pack(fill="x", side="bottom")
        self.statusbar.pack_propagate(False)

        self.status_label = ctk.CTkLabel(
            self.statusbar, text="✅ Prêt — En attente d'action",
            font=ctk.CTkFont("Courier New", 10),
            text_color=THEME["text_sec"]
        )
        self.status_label.pack(side="left", padx=12)

        self.ai_status = ctk.CTkLabel(
            self.statusbar,
            text="🤖 IA : initialisation...",
            font=ctk.CTkFont("Courier New", 10),
            text_color=THEME["text_muted"]
        )
        self.ai_status.pack(side="right", padx=12)

        # Indicateur progression
        self.progress = ctk.CTkProgressBar(self.statusbar, width=200, height=8,
                                            fg_color=THEME["bg_card2"],
                                            progress_color=THEME["blue"])
        self.progress.pack(side="right", padx=8)
        self.progress.set(0)

    # =========================================================================
    #  ACTIONS — GÉNÉRATION DONNÉES IoMT
    # =========================================================================
    def _generate_iomt_data(self):
        self._set_status("🔄 Génération des données IoMT...", THEME["orange"])
        self._animate_progress()

        profile = self.profile_var.get()
        pid = self.patient_id_var.get() or None
        self.iomt_data = IoMTGenerator.generate(pid, profile)

        # Mise à jour métriques
        for key, lbl in self.metric_labels.items():
            val = self.iomt_data.get(key, "--")
            lbl.configure(text=str(val))

        # Couleur selon profil
        color_map = {"Normal": THEME["green"], "Critique": THEME["red"],
                     "Anomalie": THEME["warning"]}
        c = color_map.get(profile, THEME["cyan"])
        for lbl in self.metric_labels.values():
            lbl.configure(text_color=c)

        # JSON
        self.iomt_text.configure(state="normal")
        self.iomt_text.delete("1.0", "end")
        self.iomt_text.insert("1.0", json.dumps(self.iomt_data, indent=2, ensure_ascii=False))
        self.iomt_text.configure(state="disabled")

        self._log(f"[IoMT] Données générées — Profil: {profile} | Patient: {self.iomt_data['patient_id']}")
        self._set_status("✅ Données IoMT générées", THEME["green"])
        self.progress.set(1.0)

    # =========================================================================
    #  ACTIONS — GÉNÉRATION CLÉS ECC
    # =========================================================================
    def _generate_keys(self):
        curve = self.curve_var.get()
        self.ecc = ECCCrypto(curve)
        self._set_status(f"🔑 Génération des clés ECC ({curve})...", THEME["orange"])
        self._animate_progress()

        self.key_info = self.ecc.generate_keys()

        # Mise à jour badges
        self.key_badges["curve"].configure(text=self.key_info["curve"])
        self.key_badges["key_size"].configure(text=f"{self.key_info['key_size']} bits")
        self.key_badges["gen_time_ms"].configure(
            text=f"{self.key_info['gen_time_ms']} ms")

        # Clé publique
        self.pub_key_text.configure(state="normal")
        self.pub_key_text.delete("1.0", "end")
        self.pub_key_text.insert("1.0", self.key_info["public_pem"])
        self.pub_key_text.configure(state="disabled")

        # Clé privée
        self.priv_key_text.configure(state="normal")
        self.priv_key_text.delete("1.0", "end")
        self.priv_key_text.insert("1.0", self.key_info["private_pem"])
        self.priv_key_text.configure(state="disabled")

        self._log(f"[ECC] Clés générées — Courbe: {curve} | "
                  f"Temps: {self.key_info['gen_time_ms']} ms")
        self._set_status(f"✅ Clés ECC ({curve}) générées", THEME["green"])
        self.progress.set(1.0)

    # =========================================================================
    #  ACTIONS — CHIFFREMENT
    # =========================================================================
    def _encrypt_data(self):
        if not self.iomt_data:
            self._show_warn("Générez d'abord les données IoMT (onglet 📊)")
            return
        if not self.ecc.public_key:
            self._generate_keys()

        self._set_status("🔒 Chiffrement ECIES en cours...", THEME["orange"])
        self._animate_progress()

        plaintext = json.dumps(self.iomt_data, ensure_ascii=False)
        self.enc_result = self.ecc.encrypt(plaintext)

        # Étapes
        self.steps_text.configure(state="normal")
        self.steps_text.delete("1.0", "end")
        for step in self.enc_result["steps"]:
            self.steps_text.insert("end", step + "\n")
        self.steps_text.configure(state="disabled")

        # Badges
        self.enc_badges["enc_time_ms"].configure(
            text=f"{self.enc_result['enc_time_ms']} ms")
        self.enc_badges["plaintext_len"].configure(
            text=f"{self.enc_result['plaintext_len']} o")
        self.enc_badges["ciphertext_len"].configure(
            text=f"{self.enc_result['ciphertext_len']} o")

        # Ciphertext
        self.cipher_text.configure(state="normal")
        self.cipher_text.delete("1.0", "end")
        self.cipher_text.insert("1.0", self.enc_result["ciphertext_b64"])
        self.cipher_text.configure(state="disabled")

        # Détails
        details = (
            f"Secret partagé (ECDH) : {self.enc_result['shared_secret_hex'][:48]}...\n"
            f"Clé AES-256 (HKDF)    : {self.enc_result['aes_key_hex']}\n"
            f"Nonce (96-bit)         : {self.enc_result['nonce_hex']}\n"
            f"Tag GCM (128-bit)      : {self.enc_result['tag_hex']}\n"
            f"Clé éphémère (pub PEM) :\n{self.enc_result['ephemeral_pub_pem'][:120]}..."
        )
        self.enc_details_text.configure(state="normal")
        self.enc_details_text.delete("1.0", "end")
        self.enc_details_text.insert("1.0", details)
        self.enc_details_text.configure(state="disabled")

        # Historique perf
        self.perf_history.append({
            "curve": self.curve_var.get(),
            "enc_ms": self.enc_result["enc_time_ms"],
            "size": self.enc_result["plaintext_len"],
        })

        self._log(f"[ECC] Chiffrement OK | Temps: {self.enc_result['enc_time_ms']} ms | "
                  f"Taille: {self.enc_result['plaintext_len']}→{self.enc_result['ciphertext_len']} o")
        self._set_status("✅ Données chiffrées avec succès", THEME["green"])
        self.progress.set(1.0)

    # =========================================================================
    #  ACTIONS — DÉCHIFFREMENT
    # =========================================================================
    def _decrypt_data(self):
        if not self.enc_result:
            self._show_warn("Chiffrez d'abord les données (onglet 🔐)")
            return

        self._set_status("🔓 Déchiffrement en cours...", THEME["orange"])
        self._animate_progress()

        self.dec_result = self.ecc.decrypt(self.enc_result)

        # Badge vérification
        if self.dec_result["verified"]:
            self.verify_badge.configure(
                text="✅  INTÉGRITÉ VÉRIFIÉE — Données identiques à l'original",
                fg_color=THEME["green_dark"], text_color="white"
            )
        else:
            self.verify_badge.configure(
                text="❌  ERREUR — Données corrompues ou modifiées",
                fg_color=THEME["red"], text_color="white"
            )

        self.dec_badges["dec_time_ms"].configure(
            text=f"{self.dec_result['dec_time_ms']} ms")
        self.dec_badges["verified"].configure(
            text="✅ OUI" if self.dec_result["verified"] else "❌ NON",
            text_color=THEME["green"] if self.dec_result["verified"] else THEME["red"]
        )

        self.dec_text.configure(state="normal")
        self.dec_text.delete("1.0", "end")
        try:
            pretty = json.dumps(
                json.loads(self.dec_result["decrypted_text"]),
                indent=2, ensure_ascii=False
            )
        except Exception:
            pretty = self.dec_result["decrypted_text"]
        self.dec_text.insert("1.0", pretty)
        self.dec_text.configure(state="disabled")

        self._log(f"[ECC] Déchiffrement OK | Temps: {self.dec_result['dec_time_ms']} ms | "
                  f"Vérifié: {self.dec_result['verified']}")
        self._set_status("✅ Déchiffrement réussi — Intégrité vérifiée", THEME["green"])
        self.progress.set(1.0)

    # =========================================================================
    #  ACTIONS — ANALYSE IA
    # =========================================================================
    def _run_ai_analysis(self):
        if not self.iomt_data:
            self._show_warn("Générez d'abord des données IoMT")
            return

        self._set_status("🧠 Analyse IA en cours...", THEME["purple"])
        self._animate_progress()

        data_size = len(json.dumps(self.iomt_data).encode())
        profile   = self.iomt_data.get("profile", "Normal")
        battery   = float(self.iomt_data.get("battery_pct", 75))
        signal    = self.iomt_data.get("signal_quality", "Bon")

        self.ai_result = self.ai_optimizer.recommend(
            data_size, profile, battery, signal
        )

        # Affichage résultat
        report = (
            f"━━━ RECOMMANDATION IA ━━━\n"
            f"Courbe recommandée  : {self.ai_result['recommended_curve']}\n"
            f"Confiance DT        : {self.ai_result['confidence_pct']}%\n"
            f"Temps prédit (LR)   : {self.ai_result['predicted_time_ms']} ms\n\n"
            f"━━━ ENTRÉES ━━━\n"
            f"Taille données      : {data_size} octets\n"
            f"Profil patient      : {profile}\n"
            f"Batterie capteur    : {battery:.0f}%\n"
            f"Qualité signal      : {signal}\n\n"
            f"━━━ RAISONNEMENT ━━━\n"
            f"{self.ai_result['reasoning']}\n\n"
            f"━━━ MODÈLES UTILISÉS ━━━\n"
            f"• DecisionTree (profondeur 5)\n"
            f"  → Classe feature importance :\n"
            f"     criticality  : 45%\n"
            f"     battery_pct  : 28%\n"
            f"     data_size    : 18%\n"
            f"     signal_qual  : 9%\n\n"
            f"• LinearRegression\n"
            f"  → R² estimé : 0.94\n"
            f"  → RMSE estimé : 0.6 ms"
        )
        self.ai_result_text.configure(state="normal")
        self.ai_result_text.delete("1.0", "end")
        self.ai_result_text.insert("1.0", report)
        self.ai_result_text.configure(state="disabled")

        # Appliquer la recommandation
        self.curve_var.set(self.ai_result["recommended_curve"])

        # Graphique IA
        self._draw_ai_chart()

        self._log(f"[IA] Recommandation: {self.ai_result['recommended_curve']} | "
                  f"Confiance: {self.ai_result['confidence_pct']}% | "
                  f"Temps prédit: {self.ai_result['predicted_time_ms']} ms")
        self._set_status(
            f"✅ IA → {self.ai_result['recommended_curve']} recommandée "
            f"({self.ai_result['confidence_pct']}% confiance)",
            THEME["purple"]
        )
        self.progress.set(1.0)

    # =========================================================================
    #  ACTIONS — PUBLICATION IPFS
    # =========================================================================
    def _publish_ipfs(self):
        if not self.enc_result:
            self._show_warn("Chiffrez d'abord les données (onglet 🔐)")
            return

        self._set_status("📤 Publication sur IPFS simulé...", THEME["cyan"])
        self._animate_progress()

        # Préparer le paquet à publier
        package = {
            "version":       "1.0",
            "schema":        "IoMT-ECC-IPFS",
            "timestamp":     datetime.datetime.now().isoformat(),
            "curve":         self.curve_var.get(),
            "ciphertext":    self.enc_result["ciphertext_b64"],
            "nonce":         self.enc_result["nonce_hex"],
            "tag":           self.enc_result["tag_hex"],
            "ephemeral_pub": self.enc_result["ephemeral_pub_pem"],
        }
        payload = json.dumps(package, ensure_ascii=False)

        self.ipfs_result = IPFSSimulator.add(payload, "iomt_encrypted.json")

        # Mise à jour UI
        self.cid_label.configure(text=f"📎  {self.ipfs_result['cid']}")
        self.ipfs_badges["size_bytes"].configure(
            text=f"{self.ipfs_result['size_bytes']} o")
        self.ipfs_badges["sha256"].configure(
            text=self.ipfs_result["sha256"][:20] + "...")
        self.ipfs_badges["pin_status"].configure(text="📌 Pinned")
        self.ipfs_badges["store_time_ms"].configure(
            text=f"{self.ipfs_result['store_time_ms']} ms")

        details = (
            f"CID         : {self.ipfs_result['cid']}\n"
            f"Gateway URL : {self.ipfs_result['gateway_url']}\n"
            f"SHA-256     : {self.ipfs_result['sha256']}\n"
            f"Taille      : {self.ipfs_result['size_bytes']} octets\n"
            f"Pin Status  : {self.ipfs_result['pin_status']}\n"
            f"Temps store : {self.ipfs_result['store_time_ms']} ms"
        )
        self.ipfs_detail_text.configure(state="normal")
        self.ipfs_detail_text.delete("1.0", "end")
        self.ipfs_detail_text.insert("1.0", details)
        self.ipfs_detail_text.configure(state="disabled")

        # Redessiner réseau IPFS avec nouveau nœud
        self._draw_ipfs_network(active_cid=self.ipfs_result["cid"])

        self._log(f"[IPFS] Publié | CID: {self.ipfs_result['cid'][:32]}... | "
                  f"Taille: {self.ipfs_result['size_bytes']} o")
        self._set_status(f"✅ IPFS — CID: {self.ipfs_result['cid'][:24]}...",
                         THEME["cyan"])
        self.progress.set(1.0)

    # =========================================================================
    #  ACTIONS — SIMULATION COMPLÈTE
    # =========================================================================
    def _run_full_simulation(self):
        """Lance toutes les étapes en séquence avec délai animé."""
        def _run():
            steps = [
                ("📊 Génération IoMT...", self._generate_iomt_data, 0.3),
                ("🤖 Analyse IA...",      self._run_ai_analysis,     0.3),
                ("🗝️  Génération clés...", self._generate_keys,       0.4),
                ("🔒 Chiffrement...",     self._encrypt_data,         0.4),
                ("🔓 Déchiffrement...",   self._decrypt_data,          0.3),
                ("📦 Publication IPFS...",self._publish_ipfs,          0.4),
                ("📈 Benchmark...",       self._run_benchmark,         0.5),
            ]
            for msg, fn, delay in steps:
                self.after(0, lambda m=msg: self._set_status(m, THEME["orange"]))
                time.sleep(delay)
                try:
                    self.after(0, fn)
                    time.sleep(delay)
                except Exception as e:
                    self._log(f"[ERR] {msg}: {e}")
            self.after(0, lambda: self._set_status(
                "✅ Simulation complète terminée !", THEME["green"]))

        threading.Thread(target=_run, daemon=True).start()

    # =========================================================================
    #  ACTIONS — BENCHMARK
    # =========================================================================
    def _run_benchmark(self):
        self._set_status("🔬 Benchmark ECC vs RSA en cours (peut prendre ~5s)...",
                         THEME["warning"])

        def _bench():
            # ECC benchmark (3 courbes)
            ecc_results = []
            for curve_name in ["secp256k1", "secp384r1", "secp521r1"]:
                ec = ECCCrypto(curve_name)
                ki = ec.generate_keys()
                msg = "x" * 400
                er = ec.encrypt(msg)
                ecc_results.append({
                    "name":    curve_name,
                    "bits":    ki["key_size"],
                    "key_ms":  ki["gen_time_ms"],
                    "enc_ms":  er["enc_time_ms"],
                })

            # RSA benchmark
            rsa_results = RSABenchmark.benchmark([1024, 2048, 3072])

            self.after(0, lambda: self._draw_benchmark_chart(ecc_results, rsa_results))
            self.after(0, lambda: self._set_status(
                "✅ Benchmark terminé", THEME["green"]))
            self.after(0, lambda: self.progress.set(1.0))

        threading.Thread(target=_bench, daemon=True).start()

    # =========================================================================
    #  GRAPHIQUES
    # =========================================================================
    def _draw_ai_placeholder(self):
        self.ai_fig.clf()
        ax = self.ai_fig.add_subplot(111)
        ax.set_facecolor(THEME["bg_card"])
        ax.text(0.5, 0.5, "Lancez l'analyse IA\npour voir la visualisation",
                ha="center", va="center",
                color=THEME["text_muted"], fontsize=12,
                transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_color(THEME["border"])
        self.ai_canvas.draw()

    def _draw_ai_chart(self):
        """Graphique de l'espace de décision IA."""
        if not self.ai_optimizer.trained:
            return
        self.ai_fig.clf()

        # Générer grille de prédiction
        N = 80
        sizes   = np.linspace(100, 2000, N)
        bats    = np.linspace(10, 100, N)
        S, B    = np.meshgrid(sizes, bats)
        flat_X  = np.column_stack([S.ravel(), np.ones(N*N),
                                   B.ravel(), np.ones(N*N)])
        preds   = self.ai_optimizer.dt_model.predict(flat_X).reshape(N, N)

        ax = self.ai_fig.add_subplot(111)
        ax.set_facecolor(THEME["bg_card"])

        colors = ["#1a237e", "#0277bd", "#00838f"]
        cmap   = matplotlib.colors.ListedColormap(colors)
        img    = ax.contourf(S, B, preds, levels=[-0.5,0.5,1.5,2.5],
                              colors=colors, alpha=0.75)

        if self.ai_result:
            ax.scatter(self.ai_result["data_size"],
                       self.ai_result["battery_pct"],
                       s=120, c=THEME["orange"], zorder=5,
                       marker="*", label="Cas actuel")
            ax.legend(facecolor=THEME["bg_card2"], labelcolor="white", fontsize=8)

        ax.set_xlabel("Taille données (octets)", color=THEME["text_sec"], fontsize=9)
        ax.set_ylabel("Batterie (%)", color=THEME["text_sec"], fontsize=9)
        ax.set_title("Espace de décision — Choix courbe ECC",
                     color=THEME["text_prim"], fontsize=10)
        ax.tick_params(colors=THEME["text_sec"], labelsize=8)
        for spine in ax.spines.values():
            spine.set_color(THEME["border"])

        patches = [mpatches.Patch(color=c, label=n)
                   for c, n in zip(colors, ["secp256k1","secp384r1","secp521r1"])]
        ax.legend(handles=patches, facecolor=THEME["bg_card2"],
                  labelcolor="white", fontsize=8, loc="upper right")

        self.ai_canvas.draw()

    def _draw_ipfs_network(self, active_cid: str = None):
        """Schéma réseau IPFS avec nœuds distribués."""
        self.ipfs_fig.clf()
        ax = self.ipfs_fig.add_subplot(111)
        ax.set_facecolor(THEME["bg_card"])
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 4)
        ax.axis("off")

        # Nœuds IPFS
        nodes = [
            (2, 2,   "IoMT\nDevice",    THEME["blue_dark"],  "●"),
            (5, 3,   "IPFS\nNode-1",    THEME["green_dark"], "◆"),
            (5, 1,   "IPFS\nNode-2",    THEME["green_dark"], "◆"),
            (7.5, 3, "IPFS\nNode-3",    "#6d4c41",           "◆"),
            (7.5, 1, "IPFS\nNode-4",    "#6d4c41",           "◆"),
            (9, 2,   "IPFS\nGateway",   THEME["cyan"],       "★"),
        ]
        edges = [(0,1),(0,2),(1,2),(1,3),(2,4),(3,4),(3,5),(4,5)]

        for i, (x,y,lbl,col,sym) in enumerate(nodes):
            ax.scatter(x, y, s=600, c=col, zorder=4, marker="o")
            ax.text(x, y+0.45, lbl, ha="center", va="bottom",
                    color="white", fontsize=7, zorder=5)

        for s, d in edges:
            x1,y1 = nodes[s][0], nodes[s][1]
            x2,y2 = nodes[d][0], nodes[d][1]
            color  = THEME["cyan"] if active_cid and d >= 1 else THEME["border"]
            lw     = 2 if active_cid else 0.8
            ax.plot([x1,x2],[y1,y2], color=color, lw=lw,
                    alpha=0.7, zorder=2)

        if active_cid:
            ax.text(5, 0.2, f"CID: {active_cid[:28]}...",
                    ha="center", color=THEME["cyan"],
                    fontsize=8, fontfamily="monospace")

        ax.set_title("Réseau IPFS décentralisé — IoMT data flow",
                     color=THEME["text_sec"], fontsize=9, pad=4)
        self.ipfs_canvas.draw()

    def _draw_perf_placeholder(self):
        self.perf_fig.clf()
        ax = self.perf_fig.add_subplot(111)
        ax.set_facecolor(THEME["bg_dark"])
        ax.text(0.5, 0.5, "Lancez le benchmark pour voir\nla comparaison ECC vs RSA",
                ha="center", va="center",
                color=THEME["text_muted"], fontsize=12,
                transform=ax.transAxes)
        ax.set_xticks([])
        ax.set_yticks([])
        for spine in ax.spines.values():
            spine.set_color(THEME["border"])
        self.perf_canvas.draw()

    def _draw_benchmark_chart(self, ecc_results: list, rsa_results: list):
        self.perf_fig.clf()
        self.perf_fig.set_facecolor(THEME["bg_dark"])

        # Sous-graphiques
        ax1 = self.perf_fig.add_subplot(131)
        ax2 = self.perf_fig.add_subplot(132)
        ax3 = self.perf_fig.add_subplot(133)

        for ax in [ax1, ax2, ax3]:
            ax.set_facecolor(THEME["bg_card"])
            for spine in ax.spines.values():
                spine.set_color(THEME["border"])
            ax.tick_params(colors=THEME["text_sec"], labelsize=8)

        # — Graphique 1 : Génération de clés ──────────────────────────────
        ecc_names  = [r["name"].replace("secp","") for r in ecc_results]
        ecc_keygen = [r["key_ms"] for r in ecc_results]
        rsa_names  = [f"RSA-{r['key_size']}" for r in rsa_results if "enc_ms" in r]
        rsa_keygen = [r["keygen_ms"] for r in rsa_results if "enc_ms" in r]

        x1 = np.arange(len(ecc_names))
        x2 = np.arange(len(rsa_names))

        ax1.bar(x1, ecc_keygen, color=THEME["blue"], label="ECC", alpha=0.85, width=0.4)
        if rsa_keygen:
            ax1.bar(x2 + len(x1) + 0.5, rsa_keygen,
                    color=THEME["orange"], label="RSA", alpha=0.85, width=0.4)
        ax1.set_xticks(list(x1) + list(x2+len(x1)+0.5))
        ax1.set_xticklabels(ecc_names + rsa_names, rotation=30, ha="right", fontsize=7)
        ax1.set_title("Génération de clés (ms)",
                      color=THEME["text_prim"], fontsize=9)
        ax1.set_ylabel("ms", color=THEME["text_sec"], fontsize=8)
        ax1.legend(facecolor=THEME["bg_card2"], labelcolor="white", fontsize=7)

        # — Graphique 2 : Temps de chiffrement ─────────────────────────────
        ecc_enc = [r["enc_ms"] for r in ecc_results]
        rsa_enc = [r["enc_ms"] for r in rsa_results if "enc_ms" in r]

        ax2.bar(x1, ecc_enc, color=THEME["green"], label="ECC", alpha=0.85, width=0.4)
        if rsa_enc:
            ax2.bar(x2 + len(x1) + 0.5, rsa_enc,
                    color=THEME["red"], label="RSA", alpha=0.85, width=0.4)
        ax2.set_xticks(list(x1) + list(x2+len(x1)+0.5))
        ax2.set_xticklabels(ecc_names + rsa_names, rotation=30, ha="right", fontsize=7)
        ax2.set_title("Chiffrement message (ms)",
                      color=THEME["text_prim"], fontsize=9)
        ax2.set_ylabel("ms", color=THEME["text_sec"], fontsize=8)
        ax2.legend(facecolor=THEME["bg_card2"], labelcolor="white", fontsize=7)

        # — Graphique 3 : Taille des clés ──────────────────────────────────
        ecc_sizes = [r["bits"] for r in ecc_results]
        rsa_sizes = [r["key_size"] for r in rsa_results if "enc_ms" in r]
        all_names = ecc_names + rsa_names
        all_sizes = ecc_sizes + rsa_sizes
        colors3   = [THEME["blue"]]*len(ecc_names) + [THEME["orange"]]*len(rsa_names)

        bars = ax3.bar(range(len(all_names)), all_sizes, color=colors3, alpha=0.85)
        ax3.set_xticks(range(len(all_names)))
        ax3.set_xticklabels(all_names, rotation=30, ha="right", fontsize=7)
        ax3.set_title("Taille des clés (bits)",
                      color=THEME["text_prim"], fontsize=9)
        ax3.set_ylabel("bits", color=THEME["text_sec"], fontsize=8)
        for bar, size in zip(bars, all_sizes):
            ax3.text(bar.get_x()+bar.get_width()/2, bar.get_height()+20,
                     str(size), ha="center", color="white", fontsize=7)

        # Note en bas
        self.perf_fig.text(0.5, 0.01,
                            "ECC offre une sécurité équivalente à RSA avec des clés ~10× plus courtes",
                            ha="center", color=THEME["text_sec"], fontsize=8)

        self.perf_canvas.draw()
        self._log("[Bench] Comparaison ECC vs RSA effectuée")

    # =========================================================================
    #  UTILITAIRES
    # =========================================================================
    def _init_ai(self):
        """Initialise l'IA en arrière-plan."""
        self.ai_optimizer.train()
        self.after(0, lambda: self.ai_status.configure(
            text="🤖 IA : prête (500 échantillons)",
            text_color=THEME["green"]
        ))

    def _set_status(self, msg: str, color: str = None):
        self.status_label.configure(
            text=msg,
            text_color=color or THEME["text_sec"]
        )

    def _animate_progress(self):
        self.progress.set(0)
        def _anim(v=0):
            v = min(v + 0.05, 0.9)
            self.progress.set(v)
            if v < 0.9:
                self.after(30, lambda: _anim(v))
        _anim()

    def _log(self, msg: str):
        ts = datetime.datetime.now().strftime("%H:%M:%S.%f")[:-3]
        line = f"[{ts}] {msg}"
        self.log_lines.append(line)
        try:
            self.log_text.configure(state="normal")
            self.log_text.insert("end", line + "\n")
            self.log_text.see("end")
            self.log_text.configure(state="disabled")
        except Exception:
            pass

    def _clear_logs(self):
        self.log_lines.clear()
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")

    def _show_warn(self, msg: str):
        messagebox.showwarning("Attention", msg, parent=self)

    def _toggle_theme(self):
        current = ctk.get_appearance_mode()
        ctk.set_appearance_mode("light" if current == "Dark" else "dark")

# =============================================================================
#  POINT D'ENTRÉE
# =============================================================================
if __name__ == "__main__":
    app = IoMTApp()
    app.mainloop()

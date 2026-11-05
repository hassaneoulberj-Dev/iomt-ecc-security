#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
================================================================================
SIMULATION IoMT - ECC - IA - IPFS
================================================================================
Sujet : La cryptographie basée sur les courbes elliptiques (ECC)
        Optimisation par IA pour sécuriser les données des capteurs IoMT
        vers IPFS.

Ce programme simule :
    1. Génération de données de capteurs médicaux (IoMT)
    2. Cryptographie ECC avec ECIES (explication détaillée)
    3. Intelligence Artificielle pour recommander la meilleure courbe
       (recommandation dynamique selon batterie et taille des données)
    4. Stockage décentralisé sur IPFS (simulation avec schéma réseau)
    5. Interface graphique complète en français
================================================================================
"""

# -----------------------------------------------------------------------------
# IMPORTS
# -----------------------------------------------------------------------------
import os
import sys
import time
import json
import random
import hashlib
import base64
import threading
import datetime
from collections import deque

import tkinter as tk
from tkinter import messagebox

try:
    import customtkinter as ctk
except ImportError:
    os.system("pip install customtkinter -q")
    import customtkinter as ctk

# Cryptographie ECC
try:
    from cryptography.hazmat.primitives.asymmetric.ec import (
        generate_private_key, SECP256K1, SECP384R1, SECP521R1, ECDH
    )
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.backends import default_backend
except ImportError:
    os.system("pip install cryptography -q")
    from cryptography.hazmat.primitives.asymmetric.ec import (
        generate_private_key, SECP256K1, SECP384R1, SECP521R1, ECDH
    )
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.backends import default_backend

# Intelligence Artificielle
try:
    import numpy as np
    from sklearn.tree import DecisionTreeClassifier
    from sklearn.preprocessing import LabelEncoder
except ImportError:
    os.system("pip install scikit-learn numpy -q")
    import numpy as np
    from sklearn.tree import DecisionTreeClassifier
    from sklearn.preprocessing import LabelEncoder

# Graphiques
try:
    import matplotlib
    matplotlib.use("TkAgg")
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    import matplotlib.patches as mpatches
except ImportError:
    os.system("pip install matplotlib -q")
    import matplotlib
    matplotlib.use("TkAgg")
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    import matplotlib.patches as mpatches

# -----------------------------------------------------------------------------
# CONFIGURATION DU THÈME (Clair - Light Mode)
# -----------------------------------------------------------------------------
THEME = {
    "bg_dark":     "#F0F4F8",   # fond principal clair (gris très clair bleuté)
    "bg_card":     "#FFFFFF",   # fond des cartes / panneaux (blanc pur)
    "bg_card2":    "#EDF2F7",   # fond secondaire (gris très clair)
    "border":      "#CBD5E0",   # bordures (gris doux)
    "blue":        "#2B6CB0",   # bleu principal foncé (lisible sur blanc)
    "blue_dark":   "#2C5282",   # bleu foncé (boutons primaires)
    "green":       "#276749",   # vert foncé (succès)
    "green_dark":  "#2F855A",   # vert moyen
    "orange":      "#C05621",   # orange foncé (avertissements)
    "red":         "#C53030",   # rouge foncé (erreurs)
    "purple":      "#553C9A",   # violet foncé (IA)
    "cyan":        "#0987A0",   # cyan foncé (IPFS)
    "text_prim":   "#1A202C",   # texte principal (quasi-noir)
    "text_sec":    "#4A5568",   # texte secondaire (gris moyen)
    "text_muted":  "#A0AEC0",   # texte atténué (gris clair)
}

ctk.set_appearance_mode("light")
ctk.set_default_color_theme("blue")

# -----------------------------------------------------------------------------
# MODULE 1 : GÉNÉRATEUR DE DONNÉES IoMT
# -----------------------------------------------------------------------------
class IoMTGenerator:
    """Simule des capteurs médicaux connectés."""

    PROFILS = {
        "Normal": {
            "temp": (36.2, 37.2), "hr": (60, 80),
            "bp_s": (110, 125), "bp_d": (70, 82),
            "spo2": (97, 100), "glucose": (80, 100),
        },
        "Critique": {
            "temp": (38.5, 40.5), "hr": (100, 145),
            "bp_s": (160, 190), "bp_d": (95, 115),
            "spo2": (85, 93), "glucose": (180, 350),
        },
        "Anomalie": {
            "temp": (34.0, 35.8), "hr": (40, 55),
            "bp_s": (85, 100), "bp_d": (50, 65),
            "spo2": (90, 95), "glucose": (50, 70),
        },
    }

    @staticmethod
    def generer(patient_id=None, profil="Normal"):
        p = IoMTGenerator.PROFILS.get(profil, IoMTGenerator.PROFILS["Normal"])
        def alea(minv, maxv, dec=1):
            return round(random.uniform(minv, maxv), dec)
        if not patient_id:
            patient_id = f"PAT-{random.randint(1000,9999)}"
        return {
            "patient_id": patient_id,
            "timestamp": datetime.datetime.now().isoformat(),
            "profil": profil,
            "temperature_C": alea(*p["temp"]),
            "rythme_cardiaque_bpm": alea(*p["hr"], 0),
            "pression_arterielle": f"{alea(*p['bp_s'],0)}/{alea(*p['bp_d'],0)}",
            "spo2_pct": alea(*p["spo2"]),
            "glucose_mgdl": alea(*p["glucose"], 0),
            "capteur_id": f"CAP-{random.randint(100,999)}",
            "modele": random.choice(["MedBand Pro", "HealthNode X3", "BioSense Ultra", "VitalTrack 5G"]),
            "batterie_pct": alea(15, 100, 0),
            "qualite_signal": random.choice(["Excellent", "Bon", "Faible"]),
        }

# -----------------------------------------------------------------------------
# MODULE 2 : CRYPTOGRAPHIE ECC (ECIES)
# -----------------------------------------------------------------------------
class ECCCrypto:
    """
    Implémente ECIES (Elliptic Curve Integrated Encryption Scheme).
    Étapes du chiffrement :
      1. Génération d'une clé éphémère (r, R = r·G)
      2. Calcul du secret partagé S = r × Q_destinataire (ECDH)
      3. Dérivation d'une clé AES-256 via HKDF(S)
      4. Chiffrement AES-256-GCM du message
      5. Envoi du paquet (R_pub, nonce, tag, ciphertext)
    """

    COURBES = {
        "secp256k1": SECP256K1,
        "secp384r1": SECP384R1,
        "secp521r1": SECP521R1,
    }

    def __init__(self, nom_courbe="secp256k1"):
        self.nom_courbe = nom_courbe
        self.courbe = self.COURBES[nom_courbe]()
        self.cle_privee = None
        self.cle_publique = None
        self.backend = default_backend()

    def generer_cles(self):
        t0 = time.perf_counter()
        self.cle_privee = generate_private_key(self.courbe, self.backend)
        self.cle_publique = self.cle_privee.public_key()
        temps = (time.perf_counter() - t0) * 1000

        priv_pem = self.cle_privee.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.PKCS8,
            encryption_algorithm=serialization.NoEncryption()
        ).decode()
        pub_pem = self.cle_publique.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo
        ).decode()

        return {
            "courbe": self.nom_courbe,
            "taille_cle": self.cle_privee.key_size,
            "cle_privee_pem": priv_pem,
            "cle_publique_pem": pub_pem,
            "temps_gen_ms": round(temps, 3),
        }

    def chiffrer(self, texte_clair):
        if not self.cle_publique:
            raise RuntimeError("Générez les clés d'abord.")
        t0 = time.perf_counter()
        etapes = []

        etapes.append("1. Génération clé éphémère (r, R = r·G)")
        cle_ephemere = generate_private_key(self.courbe, self.backend)
        cle_ephemere_pub = cle_ephemere.public_key()

        etapes.append("2. Calcul secret partagé S = r × Q_destinataire (ECDH)")
        secret = cle_ephemere.exchange(ECDH(), self.cle_publique)

        etapes.append("3. Dérivation clé AES-256 via HKDF-SHA256")
        hkdf = HKDF(algorithm=hashes.SHA256(), length=32, salt=None,
                    info=b"IoMT-ECC-v1", backend=self.backend)
        cle_aes = hkdf.derive(secret)

        etapes.append("4. Chiffrement AES-256-GCM du message")
        nonce = os.urandom(12)
        cipher = Cipher(algorithms.AES(cle_aes), modes.GCM(nonce),
                        backend=self.backend).encryptor()
        texte_bytes = texte_clair.encode("utf-8")
        ciphertext = cipher.update(texte_bytes) + cipher.finalize()
        tag = cipher.tag

        etapes.append("5. Assemblage du paquet chiffré (R_pub, nonce, tag, ciphertext)")
        ephem_pem = cle_ephemere_pub.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo
        ).decode()

        temps = (time.perf_counter() - t0) * 1000
        return {
            "texte_clair": texte_clair,
            "cle_ephemere_pem": ephem_pem,
            "secret_partage_hex": secret.hex(),
            "cle_aes_hex": cle_aes.hex(),
            "nonce_hex": nonce.hex(),
            "tag_hex": tag.hex(),
            "ciphertext_b64": base64.b64encode(ciphertext).decode(),
            "etapes": etapes,
            "temps_chiffrement_ms": round(temps, 3),
            "taille_claire": len(texte_bytes),
            "taille_chiffree": len(ciphertext),
            "_raw": {
                "cle_ephemere": cle_ephemere,
                "nonce": nonce,
                "tag": tag,
                "ciphertext": ciphertext,
            }
        }

    def dechiffrer(self, resultat_chiffrement):
        if not self.cle_privee:
            raise RuntimeError("Clé privée manquante.")
        t0 = time.perf_counter()
        raw = resultat_chiffrement["_raw"]
        secret = self.cle_privee.exchange(ECDH(), raw["cle_ephemere"].public_key())
        hkdf = HKDF(algorithm=hashes.SHA256(), length=32, salt=None,
                    info=b"IoMT-ECC-v1", backend=self.backend)
        cle_aes = hkdf.derive(secret)
        decryptor = Cipher(algorithms.AES(cle_aes),
                           modes.GCM(raw["nonce"], raw["tag"]),
                           backend=self.backend).decryptor()
        texte_dechiffre = (decryptor.update(raw["ciphertext"]) +
                           decryptor.finalize()).decode("utf-8")
        temps = (time.perf_counter() - t0) * 1000
        return {
            "texte_dechiffre": texte_dechiffre,
            "temps_dechiffrement_ms": round(temps, 3),
            "verifie": (texte_dechiffre == resultat_chiffrement["texte_clair"]),
        }

# -----------------------------------------------------------------------------
# MODULE 3 : INTELLIGENCE ARTIFICIELLE (OPTIMISATION)
# -----------------------------------------------------------------------------
class OptimiseurIA:
    """Recommande la courbe ECC optimale selon le contexte."""

    def __init__(self):
        self.modele_dt = None
        self.encodeur = LabelEncoder()
        self.entraine = False

    def entrainer(self):
        np.random.seed(42)
        N = 500
        taille = np.random.randint(100, 2000, N)
        criticite = np.random.randint(0, 3, N)
        batterie = np.random.randint(10, 100, N)
        signal = np.random.randint(0, 3, N)

        X = np.column_stack([taille, criticite, batterie, signal])
        labels = []
        for i in range(N):
            if criticite[i] == 2:
                if batterie[i] < 30:
                    labels.append("secp384r1")
                else:
                    labels.append("secp521r1")
            elif criticite[i] == 1:
                labels.append("secp384r1")
            else:
                labels.append("secp256k1")
        y = self.encodeur.fit_transform(labels)
        self.modele_dt = DecisionTreeClassifier(max_depth=5, random_state=42)
        self.modele_dt.fit(X, y)
        self.entraine = True

    def recommander(self, taille_donnees, profil, batterie_pct, qualite_signal):
        if not self.entraine:
            self.entrainer()
        criticite_num = {"Normal": 0, "Anomalie": 1, "Critique": 2}.get(profil, 0)
        signal_num = {"Faible": 0, "Bon": 1, "Excellent": 2}.get(qualite_signal, 1)
        X = np.array([[taille_donnees, criticite_num, batterie_pct, signal_num]])
        idx = self.modele_dt.predict(X)[0]
        courbe = self.encodeur.inverse_transform([idx])[0]
        confiance = float(self.modele_dt.predict_proba(X)[0].max()) * 100
        facteur = {"secp256k1": 0.08, "secp384r1": 0.15, "secp521r1": 0.25}
        temps_pred = taille_donnees * facteur[courbe] + 2.0
        return {
            "courbe_recommandee": courbe,
            "confiance_pct": round(confiance, 1),
            "temps_predi_ms": round(temps_pred, 2),
            "taille_donnees": taille_donnees,
            "profil": profil,
            "batterie_pct": batterie_pct,
            "explication": self._expliquer(courbe, profil, batterie_pct),
        }

    def _expliquer(self, courbe, profil, batterie):
        if courbe == "secp256k1":
            return f"Profil '{profil}' peu critique → courbe rapide 256 bits (économie d'énergie)."
        elif courbe == "secp384r1":
            return f"Profil '{profil}' + batterie {batterie:.0f}% → équilibre sécurité/performance."
        else:
            return f"Profil CRITIQUE + ressources suffisantes → sécurité maximale 521 bits."

# -----------------------------------------------------------------------------
# MODULE 4 : SIMULATION IPFS
# -----------------------------------------------------------------------------
class SimulateurIPFS:
    ALPHABET_BASE58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    stockage = {}

    @classmethod
    def _to_base58(cls, data):
        count = 0
        for b in data:
            if b == 0:
                count += 1
            else:
                break
        num = int.from_bytes(data, "big")
        res = ""
        while num > 0:
            num, rem = divmod(num, 58)
            res = cls.ALPHABET_BASE58[rem] + res
        return "1" * count + res

    @classmethod
    def ajouter(cls, donnees, nom_fichier="iomt.enc"):
        t0 = time.perf_counter()
        contenu = donnees.encode("utf-8")
        sha = hashlib.sha256(contenu).digest()
        multihash = bytes([0x12, 0x20]) + sha
        cid = "Qm" + cls._to_base58(multihash)[:44]
        cls.stockage[cid] = {
            "contenu": donnees,
            "nom": nom_fichier,
            "taille": len(contenu),
            "timestamp": datetime.datetime.now().isoformat(),
            "sha256": sha.hex(),
            "epingle": True,
        }
        temps = (time.perf_counter() - t0) * 1000
        return {
            "cid": cid,
            "taille_octets": len(contenu),
            "sha256": sha.hex(),
            "statut_epingle": "Épinglé",
            "temps_stockage_ms": round(temps, 3),
            "url_gateway": f"https://ipfs.io/ipfs/{cid}",
        }

# -----------------------------------------------------------------------------
# APPLICATION PRINCIPALE (INTERFACE GRAPHIQUE)
# -----------------------------------------------------------------------------
class ApplicationIoMT(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("🔐 Simulation IoMT - ECC - IA - IPFS")
        self.geometry("1280x820")
        self.minsize(1100, 700)
        self.configure(fg_color=THEME["bg_dark"])

        # État de l'application
        self.donnees_iomt = None
        self.ecc = ECCCrypto()
        self.infos_cles = None
        self.resultat_chiffrement = None
        self.resultat_dechiffrement = None
        self.ia = OptimiseurIA()
        self.resultat_ia = None
        self.resultat_ipfs = None

        # Variables pour mode démonstration IA
        self.batterie_demo = ctk.DoubleVar(value=75.0)
        self.taille_demo = ctk.IntVar(value=500)
        self.utiliser_donnees_reelles = ctk.BooleanVar(value=True)

        # Construction de l'interface
        self._construire_en_tete()
        self._construire_onglets()
        self._construire_barre_etat()

        threading.Thread(target=self._init_ia, daemon=True).start()

    # -------------------------------------------------------------------------
    # EN-TÊTE
    # -------------------------------------------------------------------------
    def _construire_en_tete(self):
        header = ctk.CTkFrame(self, fg_color=THEME["bg_card"], height=60, corner_radius=0,
                              border_width=1, border_color=THEME["border"])
        header.pack(fill="x", side="top")
        header.pack_propagate(False)

        ctk.CTkLabel(header, text="🔐  IoMT-ECC-IA Secure System",
                     font=ctk.CTkFont("Courier New", 20, "bold"),
                     text_color=THEME["blue"]).pack(side="left", padx=20, pady=12)

        ctk.CTkLabel(header, text="Cryptographie ECC · IA · IPFS · IoMT",
                     font=ctk.CTkFont("Courier New", 12),
                     text_color=THEME["text_sec"]).pack(side="left", padx=10)

        ctk.CTkButton(header, text="▶  Simulation Complète",
                      font=ctk.CTkFont(size=13, weight="bold"),
                      fg_color=THEME["green_dark"], hover_color=THEME["green"],
                      text_color="#FFFFFF",
                      width=180, height=36, corner_radius=8,
                      command=self._simulation_complete).pack(side="right", padx=12)

    # -------------------------------------------------------------------------
    # ONGLETS (ordre : Capteurs, IA, Chiffrement, Déchiffrement, IPFS, Performances, Logs)
    # -------------------------------------------------------------------------
    def _construire_onglets(self):
        self.tabview = ctk.CTkTabview(self, fg_color=THEME["bg_card"],
                                      segmented_button_fg_color=THEME["bg_card2"],
                                      segmented_button_selected_color=THEME["blue_dark"],
                                      segmented_button_selected_hover_color=THEME["blue"],
                                      segmented_button_unselected_color=THEME["bg_card2"],
                                      text_color=THEME["text_prim"])
        self.tabview.pack(fill="both", expand=True, padx=8, pady=(4,0))

        self.tabview.add("📊 Capteurs IoMT")
        self.tabview.add("🤖 IA Optimisation")
        self.tabview.add("🔐 Chiffrement ECC")
        self.tabview.add("🔓 Déchiffrement")
        self.tabview.add("📦 IPFS")
        self.tabview.add("📋 Logs")

        self._construire_onglet_iomt(self.tabview.tab("📊 Capteurs IoMT"))
        self._construire_onglet_ia(self.tabview.tab("🤖 IA Optimisation"))
        self._construire_onglet_chiffrement(self.tabview.tab("🔐 Chiffrement ECC"))
        self._construire_onglet_dechiffrement(self.tabview.tab("🔓 Déchiffrement"))
        self._construire_onglet_ipfs(self.tabview.tab("📦 IPFS"))
        self._construire_onglet_logs(self.tabview.tab("📋 Logs"))

    # -------------------------------------------------------------------------
    # ONGLET CAPTEURS IoMT
    # -------------------------------------------------------------------------
    def _construire_onglet_iomt(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="⚙️  Paramètres du capteur",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=THEME["blue"]).pack(anchor="w", padx=16, pady=(10,4))

        row = ctk.CTkFrame(ctrl, fg_color="transparent")
        row.pack(fill="x", padx=16, pady=(0,10))

        ctk.CTkLabel(row, text="ID Patient :", font=ctk.CTkFont(size=13),
                     text_color=THEME["text_sec"], width=90).grid(row=0,column=0,padx=4,pady=4,sticky="w")
        self.var_patient = ctk.StringVar(value="PAT-4271")
        ctk.CTkEntry(row, textvariable=self.var_patient, width=140,
                     font=("Courier New",12),
                     fg_color=THEME["bg_card2"], border_color=THEME["border"],
                     text_color=THEME["text_prim"]).grid(row=0,column=1,padx=4,pady=4)

        ctk.CTkLabel(row, text="Profil :", font=ctk.CTkFont(size=13),
                     text_color=THEME["text_sec"], width=60).grid(row=0,column=2,padx=4,pady=4,sticky="w")
        self.var_profil = ctk.StringVar(value="Normal")
        ctk.CTkOptionMenu(row, variable=self.var_profil, values=["Normal","Critique","Anomalie"],
                          fg_color=THEME["bg_card2"], button_color=THEME["blue_dark"],
                          text_color=THEME["text_prim"],
                          width=140, font=("Courier New",12)).grid(row=0,column=3,padx=4,pady=4)

        ctk.CTkButton(row, text="🔄  Générer données", font=ctk.CTkFont(size=13),
                      fg_color=THEME["blue_dark"], hover_color=THEME["blue"],
                      text_color="#FFFFFF",
                      width=160, command=self._generer_donnees).grid(row=0,column=4,padx=12,pady=4)

        # Métriques
        self.frame_metriques = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                                            border_width=1, border_color=THEME["border"])
        self.frame_metriques.pack(fill="x", padx=10, pady=4)
        self.labels_metriques = {}
        capteurs = [
            ("🌡️","Température","temperature_C","°C"),
            ("❤️","Rythme Card.","rythme_cardiaque_bpm","bpm"),
            ("🩺","Pression","pression_arterielle","mmHg"),
            ("💧","SpO₂","spo2_pct","%"),
            ("🍬","Glucose","glucose_mgdl","mg/dL"),
            ("🔋","Batterie","batterie_pct","%"),
        ]
        for i,(emoji,label,cle,unite) in enumerate(capteurs):
            card = ctk.CTkFrame(self.frame_metriques, fg_color=THEME["bg_card2"],
                                corner_radius=8, width=170, height=85,
                                border_width=1, border_color=THEME["border"])
            card.grid(row=0, column=i, padx=6, pady=6, sticky="nsew")
            card.grid_propagate(False)
            ctk.CTkLabel(card, text=f"{emoji} {label}", font=ctk.CTkFont(size=11),
                         text_color=THEME["text_sec"]).place(x=8, y=8)
            val = ctk.CTkLabel(card, text="--", font=ctk.CTkFont("Courier New", 18, "bold"),
                               text_color=THEME["blue"])
            val.place(x=8, y=30)
            ctk.CTkLabel(card, text=unite, font=ctk.CTkFont(size=10),
                         text_color=THEME["text_muted"]).place(x=8, y=58)
            self.labels_metriques[cle] = val

        self.texte_iomt = ctk.CTkTextbox(parent, height=200, fg_color=THEME["bg_card"],
                                         text_color=THEME["text_prim"], font=ctk.CTkFont("Courier New", 12),
                                         corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_iomt.pack(fill="both", expand=True, padx=10, pady=(0,8))

    # -------------------------------------------------------------------------
    # ONGLET IA OPTIMISATION (avec mode démonstration)
    # -------------------------------------------------------------------------
    def _construire_onglet_ia(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="🤖  Optimisation par Intelligence Artificielle",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=THEME["purple"]).pack(anchor="w", padx=16, pady=(10,4))

        # Zone de démonstration
        demo_frame = ctk.CTkFrame(ctrl, fg_color=THEME["bg_card2"], corner_radius=8,
                                  border_width=1, border_color=THEME["border"])
        demo_frame.pack(fill="x", padx=16, pady=8)
        ctk.CTkLabel(demo_frame, text="🎮  Mode démonstration (forcer les paramètres pour voir la courbe changer)",
                     font=ctk.CTkFont(size=12), text_color=THEME["cyan"]).pack(anchor="w", padx=8, pady=(6,2))

        self.check_demo = ctk.CTkCheckBox(demo_frame, text="Utiliser les données réelles du capteur (sinon, valeurs manuelles)",
                                          variable=self.utiliser_donnees_reelles,
                                          onvalue=True, offvalue=False,
                                          font=ctk.CTkFont(size=11),
                                          text_color=THEME["text_prim"],
                                          checkmark_color="#FFFFFF",
                                          fg_color=THEME["blue_dark"],
                                          border_color=THEME["border"],
                                          command=self._mettre_a_jour_ia)
        self.check_demo.pack(anchor="w", padx=8, pady=4)

        row_demo = ctk.CTkFrame(demo_frame, fg_color="transparent")
        row_demo.pack(fill="x", padx=8, pady=4)

        ctk.CTkLabel(row_demo, text="Batterie (%) :", font=ctk.CTkFont(size=12),
                     text_color=THEME["text_sec"]).grid(row=0, column=0, padx=4, pady=4, sticky="w")
        self.slider_batterie = ctk.CTkSlider(row_demo, from_=0, to=100, variable=self.batterie_demo,
                                             button_color=THEME["blue_dark"],
                                             progress_color=THEME["blue"],
                                             command=lambda x: self._mettre_a_jour_ia())
        self.slider_batterie.grid(row=0, column=1, padx=4, pady=4, sticky="ew")
        self.label_batterie_val = ctk.CTkLabel(row_demo, text="75%", font=ctk.CTkFont(size=12),
                                               text_color=THEME["orange"])
        self.label_batterie_val.grid(row=0, column=2, padx=4, pady=4)
        self.batterie_demo.trace_add("write", lambda *a: self.label_batterie_val.configure(text=f"{int(self.batterie_demo.get())}%"))

        ctk.CTkLabel(row_demo, text="Taille données (octets) :", font=ctk.CTkFont(size=12),
                     text_color=THEME["text_sec"]).grid(row=1, column=0, padx=4, pady=4, sticky="w")
        self.entry_taille = ctk.CTkEntry(row_demo, textvariable=self.taille_demo, width=100,
                                         font=("Courier New",12),
                                         fg_color=THEME["bg_card"], border_color=THEME["border"],
                                         text_color=THEME["text_prim"])
        self.entry_taille.grid(row=1, column=1, padx=4, pady=4, sticky="w")
        self.taille_demo.trace_add("write", lambda *a: self._mettre_a_jour_ia())
        ctk.CTkLabel(row_demo, text="(ex: 100 = petit, 2000 = grand)", font=ctk.CTkFont(size=10),
                     text_color=THEME["text_muted"]).grid(row=1, column=2, padx=4, pady=4, sticky="w")

        btn_frame = ctk.CTkFrame(ctrl, fg_color="transparent")
        btn_frame.pack(fill="x", padx=16, pady=8)
        ctk.CTkButton(btn_frame, text="🧠  Analyser & Recommander", font=ctk.CTkFont(size=13),
                      fg_color=THEME["purple"], hover_color="#6B46C1",
                      text_color="#FFFFFF",
                      width=220, command=self._analyse_ia).pack(side="left", padx=4)

        self.texte_resultat_ia = ctk.CTkTextbox(parent, height=200, fg_color=THEME["bg_card"],
                                                text_color=THEME["text_prim"],
                                                font=ctk.CTkFont("Courier New", 12),
                                                corner_radius=6,
                                                border_width=1, border_color=THEME["border"])
        self.texte_resultat_ia.pack(fill="x", padx=10, pady=(0,8))

        self.fig_ia = plt.Figure(figsize=(7, 3.5), facecolor=THEME["bg_card"], tight_layout=True)
        self.canvas_ia = FigureCanvasTkAgg(self.fig_ia, master=parent)
        self.canvas_ia.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=(0,8))
        self._dessiner_placeholder_ia()

    def _mettre_a_jour_ia(self):
        if self.resultat_ia:
            self._analyse_ia()

    # -------------------------------------------------------------------------
    # ONGLET CHIFFREMENT ECC (inspiré de hh.py)
    # -------------------------------------------------------------------------
    def _construire_onglet_chiffrement(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="🔐  Paramètres ECC",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["blue"]).pack(anchor="w", padx=16, pady=(10,4))

        row = ctk.CTkFrame(ctrl, fg_color="transparent")
        row.pack(fill="x", padx=16, pady=(0,10))

        ctk.CTkLabel(row, text="Courbe :", text_color=THEME["text_sec"]).grid(row=0, column=0, padx=4, pady=4, sticky="w")
        self.var_courbe = ctk.StringVar(value="secp256k1")
        ctk.CTkOptionMenu(row, variable=self.var_courbe, values=["secp256k1","secp384r1","secp521r1"],
                          fg_color=THEME["bg_card2"], button_color=THEME["blue_dark"],
                          text_color=THEME["text_prim"],
                          width=130).grid(row=0, column=1, padx=4, pady=4)

        ctk.CTkButton(row, text="🗝️  Générer clés", fg_color=THEME["orange"], hover_color="#DD6B20",
                      text_color="#FFFFFF", width=140, command=self._generer_cles).grid(row=0, column=2, padx=8, pady=4)

        ctk.CTkButton(row, text="🔒  Chiffrer données", fg_color=THEME["blue_dark"], hover_color=THEME["blue"],
                      text_color="#FFFFFF",
                      width=150, command=self._chiffrer).grid(row=0, column=3, padx=4, pady=4)

        # Panneau à deux colonnes
        pane = ctk.CTkFrame(parent, fg_color="transparent")
        pane.pack(fill="both", expand=True, padx=10, pady=(0,8))
        pane.columnconfigure(0, weight=1)
        pane.columnconfigure(1, weight=1)
        pane.rowconfigure(0, weight=1)

        # Colonne gauche : Clés ECC
        left = ctk.CTkFrame(pane, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        left.grid(row=0, column=0, padx=(0,4), pady=0, sticky="nsew")

        ctk.CTkLabel(left, text="🗝️  Clés ECC générées",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["orange"]).pack(anchor="w", padx=12, pady=(10,4))

        self.frame_infos_cles = ctk.CTkFrame(left, fg_color="transparent")
        self.frame_infos_cles.pack(fill="x", padx=12, pady=4)
        self.badges_cles = {}
        for badge_cle, label in [("courbe","Courbe"),("taille_cle","Taille"),("temps_gen_ms","Temps gén.")]:
            b = ctk.CTkFrame(self.frame_infos_cles, fg_color=THEME["bg_card2"], corner_radius=6,
                             border_width=1, border_color=THEME["border"])
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=label, font=ctk.CTkFont(size=9), text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            val = ctk.CTkLabel(b, text="--", font=ctk.CTkFont("Courier New", 12, "bold"), text_color=THEME["blue"])
            val.pack(padx=8, pady=(0,4))
            self.badges_cles[badge_cle] = val

        ctk.CTkLabel(left, text="Clé publique (PEM) :", font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]).pack(anchor="w", padx=12, pady=(6,2))
        self.texte_cle_publique = ctk.CTkTextbox(left, height=120, fg_color=THEME["bg_card2"],
                                                 text_color=THEME["green"], font=ctk.CTkFont("Courier New", 9),
                                                 corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_cle_publique.pack(fill="x", padx=12, pady=(0,4))

        ctk.CTkLabel(left, text="Clé privée (PEM) [⚠️ secrète] :", font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]).pack(anchor="w", padx=12, pady=(4,2))
        self.texte_cle_privee = ctk.CTkTextbox(left, height=120, fg_color=THEME["bg_card2"],
                                               text_color=THEME["red"], font=ctk.CTkFont("Courier New", 9),
                                               corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_cle_privee.pack(fill="x", padx=12, pady=(0,8))

        # Colonne droite : Résultat chiffrement
        right = ctk.CTkFrame(pane, fg_color=THEME["bg_card"], corner_radius=10,
                             border_width=1, border_color=THEME["border"])
        right.grid(row=0, column=1, padx=(4,0), pady=0, sticky="nsew")

        ctk.CTkLabel(right, text="🔒  Résultat du chiffrement",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["blue"]).pack(anchor="w", padx=12, pady=(10,4))

        ctk.CTkLabel(right, text="Étapes du processus ECIES :", font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]).pack(anchor="w", padx=12, pady=(0,2))
        self.texte_etapes = ctk.CTkTextbox(right, height=90, fg_color=THEME["bg_card2"],
                                           text_color=THEME["purple"], font=ctk.CTkFont("Courier New", 10),
                                           corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_etapes.pack(fill="x", padx=12, pady=(0,4))

        met_row = ctk.CTkFrame(right, fg_color="transparent")
        met_row.pack(fill="x", padx=12, pady=4)
        self.badges_chiffrement = {}
        for bk, lbl in [("temps_chiffrement_ms","Temps (ms)"), ("taille_claire","Taille claire"), ("taille_chiffree","Taille chiffrée")]:
            b = ctk.CTkFrame(met_row, fg_color=THEME["bg_card2"], corner_radius=6,
                             border_width=1, border_color=THEME["border"])
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=lbl, font=ctk.CTkFont(size=9), text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            v = ctk.CTkLabel(b, text="--", font=ctk.CTkFont("Courier New", 12, "bold"), text_color=THEME["orange"])
            v.pack(padx=8, pady=(0,4))
            self.badges_chiffrement[bk] = v

        ctk.CTkLabel(right, text="Ciphertext (Base64) :", font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]).pack(anchor="w", padx=12, pady=(4,2))
        self.texte_ciphertext = ctk.CTkTextbox(right, height=80, fg_color=THEME["bg_card2"],
                                               text_color=THEME["orange"], font=ctk.CTkFont("Courier New", 9),
                                               corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_ciphertext.pack(fill="x", padx=12, pady=(0,4))

        ctk.CTkLabel(right, text="Détails cryptographiques :", font=ctk.CTkFont(size=10), text_color=THEME["text_sec"]).pack(anchor="w", padx=12, pady=(4,2))
        self.texte_details_chiffrement = ctk.CTkTextbox(right, height=100, fg_color=THEME["bg_card2"],
                                                        text_color=THEME["text_prim"], font=ctk.CTkFont("Courier New", 9),
                                                        corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_details_chiffrement.pack(fill="both", expand=True, padx=12, pady=(0,8))

    # -------------------------------------------------------------------------
    # ONGLET DÉCHIFFREMENT (inspiré de hh.py)
    # -------------------------------------------------------------------------
    def _construire_onglet_dechiffrement(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])

        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="🔓  Déchiffrement ECIES",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["green"]).pack(side="left", padx=16, pady=12)

        ctk.CTkButton(ctrl, text="🔓  Déchiffrer", fg_color=THEME["green_dark"], hover_color=THEME["green"],
                      text_color="#FFFFFF",
                      width=140, command=self._dechiffrer).pack(side="right", padx=12, pady=8)

        # Schéma du processus
        schema_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                                    border_width=1, border_color=THEME["border"])
        schema_frame.pack(fill="x", padx=10, pady=(0,6))
        ctk.CTkLabel(schema_frame, text="🔄  Processus de déchiffrement ECIES",
                     font=ctk.CTkFont(size=11, weight="bold"),
                     text_color=THEME["cyan"]).pack(anchor="w", padx=16, pady=(8,4))

        steps_canvas = ctk.CTkFrame(schema_frame, fg_color="transparent", height=70)
        steps_canvas.pack(fill="x", padx=16, pady=(0,8))
        steps_canvas.pack_propagate(False)
        etapes_dechiffrement = [
            ("📦 Paquet\nreçu", THEME["blue_dark"]),
            ("🔑 ECDH\nsecret", THEME["orange"]),
            ("🔑 HKDF\nclé AES", THEME["purple"]),
            ("🔓 AES-GCM\ndéchiff.", THEME["green_dark"]),
            ("✅ Message\noriginal", THEME["green"]),
        ]
        for i, (txt, color) in enumerate(etapes_dechiffrement):
            b = ctk.CTkFrame(steps_canvas, fg_color=color, corner_radius=8, width=120, height=56)
            b.place(x=i*148 + 10, y=7)
            ctk.CTkLabel(b, text=txt, font=ctk.CTkFont("Courier New", 10),
                         text_color="white", justify="center").place(relx=0.5, rely=0.5, anchor="center")
            if i < len(etapes_dechiffrement)-1:
                ctk.CTkLabel(steps_canvas, text="→", font=ctk.CTkFont(size=20, weight="bold"),
                             text_color=THEME["text_sec"]).place(x=i*148+132, y=18)

        result_frame = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                                    border_width=1, border_color=THEME["border"])
        result_frame.pack(fill="both", expand=True, padx=10, pady=(0,8))

        ctk.CTkLabel(result_frame, text="📄  Données déchiffrées",
                     font=ctk.CTkFont(size=12, weight="bold"),
                     text_color=THEME["green"]).pack(anchor="w", padx=16, pady=(10,4))

        self.badge_verification = ctk.CTkLabel(result_frame, text="⏳ En attente...",
                                               font=ctk.CTkFont(size=12, weight="bold"),
                                               fg_color=THEME["bg_card2"], corner_radius=8,
                                               text_color=THEME["text_sec"], padx=12, pady=6)
        self.badge_verification.pack(anchor="w", padx=16, pady=4)

        met_row = ctk.CTkFrame(result_frame, fg_color="transparent")
        met_row.pack(fill="x", padx=16, pady=4)
        self.badges_dechiffrement = {}
        for bk, lbl in [("temps_dechiffrement_ms","Temps déchiff. (ms)"), ("verifie","Intégrité vérifiée")]:
            b = ctk.CTkFrame(met_row, fg_color=THEME["bg_card2"], corner_radius=6,
                             border_width=1, border_color=THEME["border"])
            b.pack(side="left", padx=4, pady=2)
            ctk.CTkLabel(b, text=lbl, font=ctk.CTkFont(size=9), text_color=THEME["text_sec"]).pack(padx=8, pady=(4,0))
            v = ctk.CTkLabel(b, text="--", font=ctk.CTkFont("Courier New", 12, "bold"), text_color=THEME["green"])
            v.pack(padx=8, pady=(0,4))
            self.badges_dechiffrement[bk] = v

        self.texte_dechiffre = ctk.CTkTextbox(result_frame, fg_color=THEME["bg_card2"],
                                              text_color=THEME["green"], font=ctk.CTkFont("Courier New", 11),
                                              corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_dechiffre.pack(fill="both", expand=True, padx=16, pady=(4,12))

    # -------------------------------------------------------------------------
    # ONGLET IPFS (avec schéma réseau)
    # -------------------------------------------------------------------------
    def _construire_onglet_ipfs(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)

        ctk.CTkLabel(ctrl, text="📦  Simulation IPFS (InterPlanetary File System)",
                     font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=THEME["cyan"]).pack(side="left", padx=16, pady=12)

        ctk.CTkButton(ctrl, text="📤  Publier sur IPFS", font=ctk.CTkFont(size=13),
                      fg_color=THEME["cyan"], hover_color="#0694A2",
                      text_color="#FFFFFF",
                      width=180, command=self._publier_ipfs).pack(side="right", padx=12, pady=8)

        self.label_cid = ctk.CTkLabel(parent, text="En attente de publication...",
                                      font=ctk.CTkFont("Courier New", 14, "bold"),
                                      text_color=THEME["cyan"], fg_color=THEME["bg_card"],
                                      corner_radius=6, padx=12, pady=8)
        self.label_cid.pack(fill="x", padx=16, pady=4)

        self.fig_ipfs = plt.Figure(figsize=(8, 3.5), facecolor=THEME["bg_card"], tight_layout=True)
        self.canvas_ipfs = FigureCanvasTkAgg(self.fig_ipfs, master=parent)
        self.canvas_ipfs.get_tk_widget().pack(fill="both", expand=True, padx=16, pady=4)
        self._dessiner_reseau_ipfs()

        self.texte_ipfs = ctk.CTkTextbox(parent, height=120, fg_color=THEME["bg_card"],
                                         text_color=THEME["text_prim"], font=ctk.CTkFont("Courier New", 11),
                                         corner_radius=6, border_width=1, border_color=THEME["border"])
        self.texte_ipfs.pack(fill="x", padx=16, pady=(0,12))

    # -------------------------------------------------------------------------
    # ONGLET PERFORMANCES (comparaison ECC vs RSA)
    # -------------------------------------------------------------------------
    def _construire_onglet_perf(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(ctrl, text="📈  Analyse de performance — ECC vs RSA",
                     font=ctk.CTkFont(size=13, weight="bold"),
                     text_color=THEME["orange"]).pack(side="left", padx=16, pady=12)
        ctk.CTkButton(ctrl, text="🔬  Lancer benchmark", fg_color=THEME["orange"], hover_color="#DD6B20",
                      text_color="white", width=160, command=self._executer_benchmark).pack(side="right", padx=12, pady=8)

        self.fig_perf = plt.Figure(figsize=(10, 4.8), facecolor=THEME["bg_card"], tight_layout=True)
        self.canvas_perf = FigureCanvasTkAgg(self.fig_perf, master=parent)
        self.canvas_perf.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=(0,8))
        self._dessiner_placeholder_perf()

    # -------------------------------------------------------------------------
    # ONGLET LOGS
    # -------------------------------------------------------------------------
    def _construire_onglet_logs(self, parent):
        parent.configure(fg_color=THEME["bg_dark"])
        ctrl = ctk.CTkFrame(parent, fg_color=THEME["bg_card"], corner_radius=10,
                            border_width=1, border_color=THEME["border"])
        ctrl.pack(fill="x", padx=10, pady=8)
        ctk.CTkLabel(ctrl, text="📋  Journal d'événements", font=ctk.CTkFont(size=15, weight="bold"),
                     text_color=THEME["text_prim"]).pack(side="left", padx=16, pady=10)
        ctk.CTkButton(ctrl, text="🗑️  Effacer", fg_color=THEME["bg_card2"], hover_color=THEME["border"],
                      text_color=THEME["text_prim"],
                      width=100, command=self._effacer_logs).pack(side="right", padx=8, pady=8)

        self.texte_log = ctk.CTkTextbox(parent, fg_color=THEME["bg_card"], text_color=THEME["text_prim"],
                                        font=ctk.CTkFont("Courier New", 11), corner_radius=6,
                                        border_width=1, border_color=THEME["border"])
        self.texte_log.pack(fill="both", expand=True, padx=10, pady=(0,8))

    # -------------------------------------------------------------------------
    # BARRE D'ÉTAT
    # -------------------------------------------------------------------------
    def _construire_barre_etat(self):
        self.barre_etat = ctk.CTkFrame(self, fg_color=THEME["bg_card"], height=28, corner_radius=0,
                                       border_width=1, border_color=THEME["border"])
        self.barre_etat.pack(fill="x", side="bottom")
        self.barre_etat.pack_propagate(False)
        self.label_statut = ctk.CTkLabel(self.barre_etat, text="✅ Prêt",
                                         font=ctk.CTkFont("Courier New", 11),
                                         text_color=THEME["text_sec"])
        self.label_statut.pack(side="left", padx=12)

    # -------------------------------------------------------------------------
    # MÉTHODES FONCTIONNELLES
    # -------------------------------------------------------------------------
    def _log(self, msg):
        ts = datetime.datetime.now().strftime("%H:%M:%S.%f")[:-3]
        ligne = f"[{ts}] {msg}"
        try:
            self.texte_log.configure(state="normal")
            self.texte_log.insert("end", ligne + "\n")
            self.texte_log.see("end")
            self.texte_log.configure(state="disabled")
        except:
            pass

    def _definir_statut(self, msg, couleur=None):
        self.label_statut.configure(text=msg, text_color=couleur or THEME["text_sec"])

    def _init_ia(self):
        self.ia.entrainer()
        self._log("[IA] Modèle entraîné avec 500 échantillons")

    def _generer_donnees(self):
        self._definir_statut("Génération des données IoMT...", THEME["orange"])
        profil = self.var_profil.get()
        pid = self.var_patient.get() or None
        self.donnees_iomt = IoMTGenerator.generer(pid, profil)
        for cle, lbl in self.labels_metriques.items():
            val = self.donnees_iomt.get(cle, "--")
            lbl.configure(text=str(val))
        self.texte_iomt.delete("1.0", "end")
        self.texte_iomt.insert("1.0", json.dumps(self.donnees_iomt, indent=2, ensure_ascii=False))
        self._log(f"[IoMT] Données générées - Profil: {profil} - Patient: {self.donnees_iomt['patient_id']}")
        self._definir_statut("Données IoMT générées", THEME["green"])

    def _analyse_ia(self):
        self._definir_statut("Analyse IA en cours...", THEME["purple"])
        if self.utiliser_donnees_reelles.get() and self.donnees_iomt:
            taille = len(json.dumps(self.donnees_iomt).encode())
            profil = self.donnees_iomt["profil"]
            batterie = float(self.donnees_iomt["batterie_pct"])
            signal = self.donnees_iomt["qualite_signal"]
        else:
            taille = self.taille_demo.get()
            profil = self.var_profil.get()
            batterie = self.batterie_demo.get()
            signal = "Bon"
            self._log(f"[IA] Mode démo - taille forcée: {taille} o, batterie: {batterie}%")

        self.resultat_ia = self.ia.recommander(taille, profil, batterie, signal)
        rapport = f"""
━━━ RECOMMANDATION IA ━━━
Courbe recommandée  : {self.resultat_ia['courbe_recommandee']}
Confiance           : {self.resultat_ia['confiance_pct']}%
Temps chiffrement estimé : {self.resultat_ia['temps_predi_ms']} ms

━━━ CONTEXTE ━━━
Taille données      : {taille} octets
Profil patient      : {profil}
Batterie capteur    : {batterie:.0f}%
Qualité signal      : {signal}

━━━ EXPLICATION ━━━
{self.resultat_ia['explication']}
"""
        self.texte_resultat_ia.delete("1.0", "end")
        self.texte_resultat_ia.insert("1.0", rapport)
        self.var_courbe.set(self.resultat_ia['courbe_recommandee'])
        self._dessiner_graphique_ia()
        self._log(f"[IA] Recommandation: {self.resultat_ia['courbe_recommandee']} (confiance {self.resultat_ia['confiance_pct']}%)")
        self._definir_statut(f"IA → {self.resultat_ia['courbe_recommandee']} recommandée", THEME["purple"])

    def _generer_cles(self):
        courbe = self.var_courbe.get()
        self.ecc = ECCCrypto(courbe)
        self._definir_statut(f"Génération clés {courbe}...", THEME["orange"])
        self.infos_cles = self.ecc.generer_cles()
        self.badges_cles["courbe"].configure(text=self.infos_cles["courbe"])
        self.badges_cles["taille_cle"].configure(text=f"{self.infos_cles['taille_cle']} bits")
        self.badges_cles["temps_gen_ms"].configure(text=f"{self.infos_cles['temps_gen_ms']} ms")
        self.texte_cle_publique.delete("1.0", "end")
        self.texte_cle_publique.insert("1.0", self.infos_cles["cle_publique_pem"])
        self.texte_cle_privee.delete("1.0", "end")
        self.texte_cle_privee.insert("1.0", self.infos_cles["cle_privee_pem"])
        self._log(f"[ECC] Clés générées - {courbe} - {self.infos_cles['temps_gen_ms']} ms")
        self._definir_statut(f"Clés {courbe} générées", THEME["green"])

    def _chiffrer(self):
        if not self.donnees_iomt:
            messagebox.showwarning("Attention", "Générez des données IoMT d'abord.", parent=self)
            return
        if not self.ecc.cle_publique:
            self._generer_cles()
        self._definir_statut("Chiffrement ECIES...", THEME["orange"])
        texte = json.dumps(self.donnees_iomt, ensure_ascii=False)
        self.resultat_chiffrement = self.ecc.chiffrer(texte)
        self.texte_etapes.delete("1.0", "end")
        for etape in self.resultat_chiffrement["etapes"]:
            self.texte_etapes.insert("end", etape + "\n")
        self.badges_chiffrement["temps_chiffrement_ms"].configure(text=f"{self.resultat_chiffrement['temps_chiffrement_ms']} ms")
        self.badges_chiffrement["taille_claire"].configure(text=f"{self.resultat_chiffrement['taille_claire']} o")
        self.badges_chiffrement["taille_chiffree"].configure(text=f"{self.resultat_chiffrement['taille_chiffree']} o")
        self.texte_ciphertext.delete("1.0", "end")
        self.texte_ciphertext.insert("1.0", self.resultat_chiffrement["ciphertext_b64"])
        details = (f"Secret partagé (ECDH) : {self.resultat_chiffrement['secret_partage_hex'][:48]}...\n"
                   f"Clé AES-256 (HKDF)    : {self.resultat_chiffrement['cle_aes_hex']}\n"
                   f"Nonce (96-bit)        : {self.resultat_chiffrement['nonce_hex']}\n"
                   f"Tag GCM (128-bit)     : {self.resultat_chiffrement['tag_hex']}")
        self.texte_details_chiffrement.delete("1.0", "end")
        self.texte_details_chiffrement.insert("1.0", details)
        self._log(f"[ECC] Chiffrement OK - temps {self.resultat_chiffrement['temps_chiffrement_ms']} ms")
        self._definir_statut("Chiffrement terminé", THEME["green"])

    def _dechiffrer(self):
        if not self.resultat_chiffrement:
            messagebox.showwarning("Attention", "Effectuez d'abord le chiffrement.", parent=self)
            return
        self._definir_statut("Déchiffrement...", THEME["orange"])
        self.resultat_dechiffrement = self.ecc.dechiffrer(self.resultat_chiffrement)
        if self.resultat_dechiffrement["verifie"]:
            self.badge_verification.configure(text="✅ INTÉGRITÉ VÉRIFIÉE - Données identiques",
                                              fg_color=THEME["green_dark"], text_color="white")
        else:
            self.badge_verification.configure(text="❌ ERREUR - Données corrompues",
                                              fg_color=THEME["red"], text_color="white")
        self.badges_dechiffrement["temps_dechiffrement_ms"].configure(text=f"{self.resultat_dechiffrement['temps_dechiffrement_ms']} ms")
        self.badges_dechiffrement["verifie"].configure(text="✅ OUI" if self.resultat_dechiffrement["verifie"] else "❌ NON")
        self.texte_dechiffre.delete("1.0", "end")
        try:
            pretty = json.dumps(json.loads(self.resultat_dechiffrement["texte_dechiffre"]), indent=2, ensure_ascii=False)
        except:
            pretty = self.resultat_dechiffrement["texte_dechiffre"]
        self.texte_dechiffre.insert("1.0", pretty)
        self._log(f"[ECC] Déchiffrement OK - vérifié: {self.resultat_dechiffrement['verifie']}")
        self._definir_statut("Déchiffrement réussi", THEME["green"])

    def _publier_ipfs(self):
        if not self.resultat_chiffrement:
            messagebox.showwarning("Attention", "Chiffrez d'abord les données.", parent=self)
            return
        self._definir_statut("Publication IPFS...", THEME["cyan"])
        paquet = {
            "version": "1.0",
            "timestamp": datetime.datetime.now().isoformat(),
            "courbe": self.var_courbe.get(),
            "ciphertext": self.resultat_chiffrement["ciphertext_b64"],
            "nonce": self.resultat_chiffrement["nonce_hex"],
            "tag": self.resultat_chiffrement["tag_hex"],
            "cle_ephemere_pub": self.resultat_chiffrement["cle_ephemere_pem"],
        }
        payload = json.dumps(paquet, ensure_ascii=False)
        self.resultat_ipfs = SimulateurIPFS.ajouter(payload, "iomt_chiffre.json")
        self.label_cid.configure(text=f"📎  {self.resultat_ipfs['cid']}")
        info = f"CID : {self.resultat_ipfs['cid']}\nTaille : {self.resultat_ipfs['taille_octets']} octets\nSHA-256 : {self.resultat_ipfs['sha256']}\nStatut : {self.resultat_ipfs['statut_epingle']}\nTemps : {self.resultat_ipfs['temps_stockage_ms']} ms\nGateway : {self.resultat_ipfs['url_gateway']}"
        self.texte_ipfs.delete("1.0", "end")
        self.texte_ipfs.insert("1.0", info)
        self._dessiner_reseau_ipfs(cid_actif=self.resultat_ipfs["cid"])
        self._log(f"[IPFS] Publié - CID: {self.resultat_ipfs['cid'][:32]}...")
        self._definir_statut(f"IPFS : {self.resultat_ipfs['cid'][:24]}...", THEME["cyan"])

    def _simulation_complete(self):
        def exec():
            self.after(0, self._generer_donnees)
            time.sleep(1)
            self.after(0, self._analyse_ia)
            time.sleep(1)
            self.after(0, self._generer_cles)
            time.sleep(0.8)
            self.after(0, self._chiffrer)
            time.sleep(1)
            self.after(0, self._dechiffrer)
            time.sleep(0.8)
            self.after(0, self._publier_ipfs)
            time.sleep(0.5)
            self.after(0, self._executer_benchmark)
        threading.Thread(target=exec, daemon=True).start()
        self._definir_statut("Simulation complète lancée", THEME["orange"])

    def _executer_benchmark(self):
        self._definir_statut("Benchmark ECC vs RSA...", THEME["orange"])
        def _bench():
            # ECC benchmark
            resultats_ecc = []
            for nom in ["secp256k1", "secp384r1", "secp521r1"]:
                ec = ECCCrypto(nom)
                ki = ec.generer_cles()
                msg = "x" * 400
                er = ec.chiffrer(msg)
                resultats_ecc.append({
                    "nom": nom, "bits": ki["taille_cle"],
                    "temps_gen_ms": ki["temps_gen_ms"],
                    "temps_chiffrement_ms": er["temps_chiffrement_ms"],
                })
            # RSA benchmark simplifié
            from cryptography.hazmat.primitives.asymmetric import rsa, padding
            resultats_rsa = []
            for taille in [1024, 2048, 3072]:
                try:
                    t0 = time.perf_counter()
                    priv = rsa.generate_private_key(public_exponent=65537, key_size=taille, backend=default_backend())
                    temps_gen = (time.perf_counter() - t0) * 1000
                    pub = priv.public_key()
                    msg = b"x" * 190
                    t1 = time.perf_counter()
                    pub.encrypt(msg, padding.OAEP(mgf=padding.MGF1(hashes.SHA256()), algorithm=hashes.SHA256(), label=None))
                    temps_chiff = (time.perf_counter() - t1) * 1000
                    resultats_rsa.append({"taille_cle": taille, "temps_gen_ms": round(temps_gen,2), "temps_chiffrement_ms": round(temps_chiff,2)})
                except:
                    pass
            self.after(0, lambda: self._dessiner_graphique_benchmark(resultats_ecc, resultats_rsa))
            self.after(0, lambda: self._definir_statut("Benchmark terminé", THEME["green"]))
        threading.Thread(target=_bench, daemon=True).start()

    # -------------------------------------------------------------------------
    # GRAPHIQUES
    # -------------------------------------------------------------------------
    def _dessiner_placeholder_ia(self):
        self.fig_ia.clf()
        ax = self.fig_ia.add_subplot(111)
        ax.set_facecolor(THEME["bg_card2"])
        ax.text(0.5, 0.5, "Lancez l'analyse IA pour voir l'espace de décision", ha="center", va="center",
                color=THEME["text_muted"], fontsize=12, transform=ax.transAxes)
        ax.set_xticks([]); ax.set_yticks([])
        for spine in ax.spines.values(): spine.set_color(THEME["border"])
        self.canvas_ia.draw()

    def _dessiner_graphique_ia(self):
        if not self.ia.entraine:
            return
        self.fig_ia.clf()
        N = 80
        tailles = np.linspace(100, 2000, N)
        batteries = np.linspace(10, 100, N)
        S, B = np.meshgrid(tailles, batteries)
        X_flat = np.column_stack([S.ravel(), np.zeros(N*N), B.ravel(), np.ones(N*N)])
        pred = self.ia.modele_dt.predict(X_flat).reshape(N, N)
        ax = self.fig_ia.add_subplot(111)
        ax.set_facecolor(THEME["bg_card2"])
        couleurs = ["#BEE3F8","#90CDF4","#63B3ED"]
        ax.contourf(S, B, pred, levels=[-0.5,0.5,1.5,2.5], colors=couleurs, alpha=0.85)
        if self.resultat_ia:
            ax.scatter(self.resultat_ia["taille_donnees"], self.resultat_ia["batterie_pct"],
                       s=150, c=THEME["orange"], marker="*", label="Cas actuel", zorder=5)
            ax.legend(facecolor=THEME["bg_card"], labelcolor=THEME["text_prim"], fontsize=10)
        ax.set_xlabel("Taille données (octets)", color=THEME["text_sec"], fontsize=11)
        ax.set_ylabel("Batterie (%)", color=THEME["text_sec"], fontsize=11)
        ax.set_title("Espace de décision - Choix de la courbe ECC (profil Normal)", color=THEME["text_prim"], fontsize=12)
        ax.tick_params(colors=THEME["text_sec"], labelsize=9)
        for spine in ax.spines.values(): spine.set_color(THEME["border"])
        patches = [mpatches.Patch(color=c, label=n) for c,n in zip(couleurs,["secp256k1","secp384r1","secp521r1"])]
        ax.legend(handles=patches, facecolor=THEME["bg_card"], labelcolor=THEME["text_prim"], fontsize=10, loc="upper right")
        self.canvas_ia.draw()

    def _dessiner_reseau_ipfs(self, cid_actif=None):
        self.fig_ipfs.clf()
        ax = self.fig_ipfs.add_subplot(111)
        ax.set_facecolor(THEME["bg_card"])
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 4)
        ax.axis("off")
        noeuds = [
            (2, 2, "IoMT\nDevice", THEME["blue_dark"]),
            (5, 3, "IPFS\nNode-1", THEME["green_dark"]),
            (5, 1, "IPFS\nNode-2", THEME["green_dark"]),
            (7.5, 3, "IPFS\nNode-3", "#8B5E3C"),
            (7.5, 1, "IPFS\nNode-4", "#8B5E3C"),
            (9, 2, "IPFS\nGateway", THEME["cyan"]),
        ]
        connexions = [(0,1),(0,2),(1,2),(1,3),(2,4),(3,4),(3,5),(4,5)]
        for i, (x,y,lbl,col) in enumerate(noeuds):
            ax.scatter(x, y, s=600, c=col, zorder=4, marker="o")
            ax.text(x, y+0.45, lbl, ha="center", va="bottom", color=THEME["text_prim"], fontsize=7, zorder=5)
        for s,d in connexions:
            x1,y1 = noeuds[s][0], noeuds[s][1]
            x2,y2 = noeuds[d][0], noeuds[d][1]
            couleur = THEME["cyan"] if cid_actif and d >= 1 else THEME["border"]
            ep = 2 if cid_actif else 0.8
            ax.plot([x1,x2],[y1,y2], color=couleur, lw=ep, alpha=0.7, zorder=2)
        if cid_actif:
            ax.text(5, 0.2, f"CID: {cid_actif[:28]}...", ha="center", color=THEME["cyan"], fontsize=8, fontfamily="monospace")
        ax.set_title("Réseau IPFS décentralisé — Flux de données IoMT", color=THEME["text_sec"], fontsize=9, pad=4)
        self.canvas_ipfs.draw()

    def _dessiner_placeholder_perf(self):
        self.fig_perf.clf()
        ax = self.fig_perf.add_subplot(111)
        ax.set_facecolor(THEME["bg_card2"])
        ax.text(0.5, 0.5, "Lancez le benchmark pour voir la comparaison ECC vs RSA", ha="center", va="center",
                color=THEME["text_muted"], fontsize=12, transform=ax.transAxes)
        ax.set_xticks([]); ax.set_yticks([])
        for spine in ax.spines.values(): spine.set_color(THEME["border"])
        self.canvas_perf.draw()

    def _dessiner_graphique_benchmark(self, ecc, rsa):
        self.fig_perf.clf()
        self.fig_perf.set_facecolor(THEME["bg_card"])
        ax1 = self.fig_perf.add_subplot(131)
        ax2 = self.fig_perf.add_subplot(132)
        ax3 = self.fig_perf.add_subplot(133)
        for ax in [ax1,ax2,ax3]:
            ax.set_facecolor(THEME["bg_card2"])
            for spine in ax.spines.values(): spine.set_color(THEME["border"])
            ax.tick_params(colors=THEME["text_sec"], labelsize=8)
        noms_ecc = [r["nom"].replace("secp","") for r in ecc]
        temps_gen_ecc = [r["temps_gen_ms"] for r in ecc]
        noms_rsa = [f"RSA-{r['taille_cle']}" for r in rsa]
        temps_gen_rsa = [r["temps_gen_ms"] for r in rsa]
        x1 = np.arange(len(noms_ecc))
        x2 = np.arange(len(noms_rsa))
        ax1.bar(x1, temps_gen_ecc, color=THEME["blue"], label="ECC", width=0.4)
        if temps_gen_rsa:
            ax1.bar(x2 + len(x1) + 0.5, temps_gen_rsa, color=THEME["orange"], label="RSA", width=0.4)
        ax1.set_xticks(list(x1) + list(x2+len(x1)+0.5))
        ax1.set_xticklabels(noms_ecc + noms_rsa, rotation=30, ha="right", fontsize=7)
        ax1.set_title("Génération de clés (ms)", color=THEME["text_prim"], fontsize=9)
        ax1.set_ylabel("ms", color=THEME["text_sec"], fontsize=8)
        ax1.legend(facecolor=THEME["bg_card"], labelcolor=THEME["text_prim"], fontsize=7)
        temps_chiff_ecc = [r["temps_chiffrement_ms"] for r in ecc]
        temps_chiff_rsa = [r["temps_chiffrement_ms"] for r in rsa]
        ax2.bar(x1, temps_chiff_ecc, color=THEME["green"], label="ECC", width=0.4)
        if temps_chiff_rsa:
            ax2.bar(x2 + len(x1) + 0.5, temps_chiff_rsa, color=THEME["red"], label="RSA", width=0.4)
        ax2.set_xticks(list(x1) + list(x2+len(x1)+0.5))
        ax2.set_xticklabels(noms_ecc + noms_rsa, rotation=30, ha="right", fontsize=7)
        ax2.set_title("Chiffrement message (ms)", color=THEME["text_prim"], fontsize=9)
        ax2.set_ylabel("ms", color=THEME["text_sec"], fontsize=8)
        ax2.legend(facecolor=THEME["bg_card"], labelcolor=THEME["text_prim"], fontsize=7)
        tailles_ecc = [r["bits"] for r in ecc]
        tailles_rsa = [r["taille_cle"] for r in rsa]
        tous_noms = noms_ecc + noms_rsa
        toutes_tailles = tailles_ecc + tailles_rsa
        couleurs3 = [THEME["blue"]]*len(noms_ecc) + [THEME["orange"]]*len(noms_rsa)
        barres = ax3.bar(range(len(tous_noms)), toutes_tailles, color=couleurs3, alpha=0.85)
        ax3.set_xticks(range(len(tous_noms)))
        ax3.set_xticklabels(tous_noms, rotation=30, ha="right", fontsize=7)
        ax3.set_title("Taille des clés (bits)", color=THEME["text_prim"], fontsize=9)
        ax3.set_ylabel("bits", color=THEME["text_sec"], fontsize=8)
        for barre, taille in zip(barres, toutes_tailles):
            ax3.text(barre.get_x()+barre.get_width()/2, barre.get_height()+20, str(taille), ha="center", color=THEME["text_prim"], fontsize=7)
        self.fig_perf.text(0.5, 0.01, "ECC offre une sécurité équivalente à RSA avec des clés ~10× plus courtes",
                           ha="center", color=THEME["text_sec"], fontsize=8)
        self.canvas_perf.draw()

    def _effacer_logs(self):
        self.texte_log.configure(state="normal")
        self.texte_log.delete("1.0", "end")
        self.texte_log.configure(state="disabled")

# -----------------------------------------------------------------------------
# POINT D'ENTRÉE
# -----------------------------------------------------------------------------
if __name__ == "__main__":
    app = ApplicationIoMT()
    app.mainloop()
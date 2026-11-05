# IoMT-ECC — Simulation de sécurité des données

Projet académique de simulation de capteurs médicaux, de chiffrement hybride ECC et de recommandation de courbe par apprentissage automatique, avec stockage local simulant IPFS.

Auteurs indiqués dans le projet original : **OULBERJ Hassane et HASKOUK Soufiane**. Module : Sécurité des Systèmes d’Information. Encadrante : Pr. Fatima AMOUNAS. Master SIDI, FST, Université Moulay Ismaïl. L’année doit être confirmée : le README original indique juin 2025, tandis qu’un énoncé porte 2025-2026.

## Deux interfaces conservées

- `src/iomt_ecc_app.py` : interface sombre, recommandation par arbre de décision, régression et comparaison ECC/RSA. Point d’entrée proposé car documenté par le README original.
- `src/Simulation.py` : variante claire avec interface en français et recommandation par arbre de décision.

Les deux programmes sont conservés sans modification ; la version finale à présenter reste au choix des auteurs.

## Installation Windows

Python 3.10 ou ultérieur avec Tkinter est nécessaire. Les vérifications ont été exécutées avec l’environnement Python 3.12 existant du projet.

Depuis ce dossier :

```powershell
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install -r requirements.txt
.\.venv\Scripts\python.exe src\iomt_ecc_app.py
```

Pour la variante claire :

```powershell
.\.venv\Scripts\python.exe src\Simulation.py
```

Le fichier requirements.txt original est conservé. Installer les dépendances avant de lancer la variante claire : elle comporte des tentatives d’installation automatique en cas d’import manquant.

Aucun serveur MySQL, compte IPFS ou fichier de données externe n’est nécessaire. Les capteurs et données d’entraînement sont simulés.

## Parcours de démonstration

1. Générer des données de capteurs pour un profil fictif.
2. Demander une recommandation de courbe dans l’onglet IA.
3. Générer les clés, puis chiffrer les données.
4. Déchiffrer et vérifier le résultat.
5. Ajouter le paquet au stockage IPFS simulé.
6. Examiner les performances et les journaux.

## Fonctionnement et limites

Le code combine ECDH, HKDF-SHA256 et AES-256-GCM. Trois courbes sont disponibles : secp256k1, secp384r1 et secp521r1.

Il s’agit d’une démonstration pédagogique : l’interface expose des clés et des valeurs intermédiaires pour expliquer les étapes. Le paquet utilisé pour déchiffrer contient des objets Python en mémoire ; ce n’est pas un protocole de transfert autonome entre deux machines.

IPFS est simulé par un dictionnaire en mémoire. Les liens de passerelle affichés ne prouvent aucune publication sur le réseau. Dans la version sombre, la fabrication du CID ajoute un préfixe Qm à une chaîne déjà encodée puis la tronque ; ces identifiants ne doivent pas être présentés comme des CID IPFS interopérables.

L’IA apprend sur des données synthétiques et des règles prédéfinies : elle ne constitue pas une validation clinique ou une preuve d’optimalité cryptographique. Les comparaisons de performances sont pédagogiques et ne suffisent pas à conclure à un niveau de sécurité équivalent entre ECC et RSA.

## Validation

Consulter `VALIDATION.md` pour les vérifications effectuées et leurs limites.

## Avant publication

Confirmer l’année académique, choisir l’interface à mettre en avant, ajouter des captures et convenir de la licence avec le coauteur. Aucun choix de licence n’est imposé dans cette préparation.
Les documents, présentations, références et anciennes archives sont conservés hors du dépôt, dans les dossiers voisins de la copie organisée. Leur contenu et leurs droits de diffusion restent à examiner.

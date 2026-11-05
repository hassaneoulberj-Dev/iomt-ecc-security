# Vérifications effectuées

- Syntaxe Python valide pour les deux applications.
- Import des deux modules réussi avec l’environnement Python 3.12 existant du projet.
- Pour chaque application et chaque courbe secp256k1, secp384r1 et secp521r1 : génération de clés, chiffrement et récupération exacte d’un message Unicode fictif.
- Pour les six combinaisons : modification d’un octet du texte chiffré rejetée par InvalidTag.
- Les copies des 25 fichiers conservés ont été comparées à leurs sources par SHA-256.

Les fenêtres graphiques n’ont pas été testées, ni le parcours complet, l’installation dans un environnement neuf, la précision des modèles ou la pertinence des benchmarks. Ces tests ciblés ne sont pas un audit de sécurité.

Les scripts Python originaux ne sont pas modifiés. Le README original reste dans documents-a-verifier/App/README.md.

Typage Bidirectionnel pour le Calcul des Constructions Inductives
===

Mots clés : Théorie des Types, Assistants à la Preuve, Typage Bidirectionnel, Calcul des Constructions Inductives, Coq, Typage Graduel

Durant leurs plus de 50 ans d'existence, les assistants à la preuve
se sont établis comme des outils permettant un haut niveau
de fiabilité dans de nombreuses applications.
Cependant, du fait de leur complexité grandissante, la solution historique de faire confiance à
un petit noyau stable n'est plus suffisante pour avancer en évitant des bugs critiques.
Mais les assistants à la preuve sont utilisés depuis des décennies pour certifier la
correction de programmes, pourquoi pas la leur ?
C'est l'ambition du projet MetaCoq,
visant à construire le premier noyau réaliste à la correction formellement prouvée,
pour l'assistant à la preuve Coq.
Ne faites plus confiance au programme, seulement à sa preuve !

Cette thèse étudie la structure bidirectionnelle qui sous-tend
l'algorithme de typage implémenté par le noyau de Coq,
dans le contexte du Calcul des Constructions Inductives (CIC) qui fonde celui-ci.
Le tout est formalisé dans le cadre de MetaCoq, et constitue
un passage obligé pour atteindre l'objectif du projet, fournissant
un intermédiaire entre l’implémentation et sa spécification.
Enfin, le contrôle renforcé sur le calcul offert par le typage bidirectionnel
est une pièce nécessaire à la conception d'une extension graduelle
de CIC, qui vise à apporter au développement en Coq la flexibilité
du typage dynamique et constitue la dernière partie de la thèse.

Bidirectional Typing for the Calculus of Inductive Constructions
===

Keywords: Type Theory, Proof Assistant, Bidirectional Typing, Calculus of Inductive Constructions, Coq, Gradual Typing

Over their more than 50 years of existence, proof assistants have established themselves as
tools guaranteeing high trust levels in many applications.
Yet, due to their increasing complexity, the historical solution of relying on a
small, trusted kernel is not enough any more to avoid critical bugs while moving forward.
But proof assistants have been used for decades to certify program correctness,
so why not their own?
This is the ambition of the MetaCoq project,
which aims at providing the first realistic kernel for a proof assistant – Coq –
to be formally proven correct, in Coq itself.
Don't trust the program any more, only its proof!
  
This thesis studies the bidirectional structure on which the typing algorithm
implemented by the kernel of Coq relies, in the context of the Calculus of
Inductive Constructions on which it is founded. This is formalized as a part of
MetaCoq, and is a key step to reach the project’s goal,
by giving an intermediate layer between the implementation and its specification.
Moreover, the increased control over computation offered by bidirectional typing
is a necessary piece in designing a gradual extension of CIC, which aims at
bringing to development in Coq the flexibility of dynamic typing,
and forms the last part of the thesis.
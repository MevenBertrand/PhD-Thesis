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

(250 words)
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

(350 words)
Over their more than 50 years of existence, proof assistants have established themselves as tools guaranteeing high trust levels in many applications. Yet, due to their ever increasing complexity, the historical solution of relying on a small, trusted kernel is not enough any more to avoid critical bugs while moving forward. But proof assistants have been used for decades to certify program correctness, why not \emph{their own}? This is the ambition of the MetaCoq project, which aims at providing the first kernel for a real-life proof assistant–Coq– that formally proven correct, in Coq itself. Don't trust the kernel any more, only its correctness proof! To that aim, this thesis studies the bidirectional structure which underpins the typing algorithm implemented by the kernel of Coq, in the context of the Calculus of Inductive Constructions on which said kernel is founded.

It first considers this bidirectional structure from a theoretical point of view. It exposes a bidirectional presentation of CIC, together the general discipline that led to it. Follow a  roof of equivalence between this presentation and the standard one. This equivalence is then used to establish properties of CIC that are hard to obtain in the standard setting–existence of principal types, and strengthening–, showing the power of this approach in studying the meta-theory of (dependent) type systems.

The second part sets on to formalize the idea of the first one in the setting of the MetaCoq project, and to use them to show correctness of the kernel. The formalized bidirectional structure supplies an intermediate between the high-level specification and the algorithm, which is key in order to prove that the kernel is complete.

Finally, the last part considers the question of designing an extension of CIC along ideas from gradual typing, with the aim of incorporanting some form of dynamic type-checking to bring more flexibility to development in Coq. The bidirectional structure is once again crucial, as the characteristics of gradual typing–in particular the way it relaxes conversion–make it impossible to base this extension on the standard presentations of CIC.
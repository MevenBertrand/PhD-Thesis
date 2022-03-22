Meven Lennon-Bertrand's PhD thesis
=========================================

This is the source for my PhD thesis. It owes a lot to the nice kaobook template, many
thanks to its contributors!

Release
-----------------------------

Releases are available [here](https://github.com/MevenBertrand/PhD-Thesis/releases), so you do not have to compile the document yourself.

Feedback
------------------------

Any feedback is extremely welcome, from tiny typos to "you should definitely change the structure of the whole thing". You can either open an issue directly here, or send me an email or message of some kind.

Build requirements
-----------------------------

If you still want to build the document yourself, you need to have the [Libertinus](https://github.com/alerque/libertinus) (including Libertinus Math) and [FiraCode](https://github.com/tonsky/FiraCode/) fonts installed.
Once this is done, you can compile using XeLaTeX with the `shell-espace` option, and biber as biblography backend.
Depending on the current commit, you might need to comment the `\includeonly` line in the `main.tex` file to compile the whole file.
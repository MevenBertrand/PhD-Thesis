\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{livre}
\LoadClass[12pt]{book}

% ---------- Mise en page ----------

% INTERLIGNES
\RequirePackage{setspace}
\setstretch{1.2}

% FORMATAGE DES TITRES
\RequirePackage{titlesec}
	\titleformat{\part}[display]{\sffamily\LARGE}{\textbf{\thepart}}{2ex}{\huge}[]
		\assignpagestyle{\part}{empty}
	\titleformat{\chapter}[display]{\sffamily\LARGE}{\textbf{\chaptertitlename\ \thechapter}}{1ex}{}[]
		\assignpagestyle{\chapter}{empty}
	\titleformat{\section}[hang]{\sffamily\bfseries\Large}{\thesection}{1em}{}[]
	\titleformat{\subsection}[hang]{\sffamily\large}{\thesubsection}{1em}{}[]

%\RequirePackage[toc,page]{appendix}
%	\addto\captionsfrench{%
%		\def\appendixname{Annexe}
%		\def\appendixtocname{Annexes}
%		\def\appendixpagename{Annexes}
%		}

% FORMATAGE DE LA TABLE DES MATIÈRES
%\RequirePackage{tocloft}

% EN-TÊTES ET PIEDS DE PAGE
\newfontfamily{\entete}[Letters=SmallCaps, LetterSpace=15, WordSpace=1.2, Ligatures=NoCommon, Numbers=OldStyle]{Roboto}
\RequirePackage{fancyhdr}
	\fancyhead[LE]{\entete\hspace*{-1.2cm}\textbf{\thepage}}
	\fancyhead[CE]{\entete\small Théorie des catégories}
	\fancyhead[CO]{\entete\small \nouppercase\leftmark}
	\fancyhead[RO]{\entete\textbf{\thepage}\hspace*{-1.2cm}}
	\fancyhead[LO,RE]{}
	\renewcommand{\headrulewidth}{0pt}
	\fancyfoot[CO,CE]{}

% LISTES
\RequirePackage{enumitem}
\setlist{
	topsep=\parskip,		% séparation verticale entre la liste et le texte
	itemsep=\parskip,		% séparation verticale entre les items
	parsep=\parskip,		% séparation verticale entre les paragraphes d'un item
	labelwidth=0.8\parindent,	% taille de la boîte contenant l'étiquette
	labelsep=0em,			% séparation entre l'étiquette et le corps de la liste
	leftmargin=\parindent,	% distance horizontale totale à gauche du corps de la liste
	align=left				% alignement de l'étiquette dans sa boîte
	}
\setlist[itemize,1]{
	label=$\blacktriangleright$
	}

% ---------- Bibliographie ----------

\RequirePackage[
	style=authoryear-ibid,
	sorting=nyt,
	maxcitenames=2,
	minbibnames=2
	]{biblatex}

\DefineBibliographyStrings{french}{
		byeditor = {dir.},
		volume   = {vol.}
		}

\renewcommand{\newunitpunct}[0]{\addcomma\addspace}
\renewcommand{\intitlepunct}{\addspace}

\DeclareFieldFormat[article,periodical]{volume}{\addcomma\addspace\bibstring{volume}\addnbspace #1\addcomma\addspace}
\DeclareFieldFormat[article,periodical]{number}{\bibstring{number}\addnbspace #1}
\renewbibmacro*{volume+number+eid}{%
	\printfield{volume}%
	\printfield{number}%
	\setunit{\addcomma\space}%
	\printfield{eid}%
	}
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{livre}
\LoadClass[12pt]{book}


% ---------- Polices ----------

\RequirePackage{fontspec}
	\setmainfont{Linux Libertine O}[Numbers=OldStyle]
	\setsansfont{Roboto}[Numbers=OldStyle, Scale=MatchUppercase]
%	\setmonofont{fontname}

% Caractères Unicode supplémentaires
\RequirePackage{newunicodechar}
	\newunicodechar{⋅}{$\cdot$}	% Point médian pour l'inclusif

% Chiffres « normaux » dans les tableaux
%\RequirePackage{etoolbox}
%\AtBeginEnvironment{tabular}{\addfontfeatures{Numbers={Lining, Monospaced}}}


% ---------- Langues ----------

\RequirePackage{polyglossia}
	\setmainlanguage{french}


% ---------- Mise en page ----------

% FORMATAGE DE LA PAGE
\RequirePackage[a4paper,
	twoside,
	inner=2cm,
	outer=3cm,
	top=1.5cm,
	bottom=1.8cm,
	includehead,
	nomarginpar
	]{geometry}

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


% ---------- Mathématiques ----------

\RequirePackage{mathtools}
%\RequirePackage{amsmath}
%\RequirePackage{amssymb}
%\RequirePackage{amsfonts}
\RequirePackage{stmaryrd}

\RequirePackage{unicode-math}
	\setmathfont{Libertinus Math}

\RequirePackage[ntheorem]{mdframed}
	\mdfdefinestyle{cadre}{
		linewidth=1pt,
		linecolor=black,
		innerrightmargin=0.6em,
		innertopmargin=10pt,
		innerbottommargin=7pt,
		innerleftmargin=0.6em,
		skipabove=\baselineskip
		}
	\mdfdefinestyle{filet}{
		linewidth=1pt,
		linecolor=black,
		bottomline=false, topline=false, rightline=false,
		innerrightmargin=0pt,
		innertopmargin=3pt,
		innerbottommargin=3pt,
		innerleftmargin=0.6em,
		skipabove=\baselineskip
		}
\RequirePackage[hyperref,amsmath,thmmarks]{ntheorem}
		\theoremheaderfont{\sffamily\scshape\bfseries}
		\theorembodyfont{\normalfont}
		\theorempreskip{0.5\topsep}
		\theorempostskip{0.5\topsep}
		\theoremstyle{nonumberbreak}
	\newmdtheoremenv[style=cadre]{defi}{Définition}
		\theoremstyle{break}
	\newmdtheoremenv[style=filet]{prop}{Proposition}[chapter]
	\newmdtheoremenv[style=cadre]{thm}[prop]{Théorème}
	\newmdtheoremenv[style=filet]{lem}[prop]{Lemme}
	\newmdtheoremenv[style=filet]{cor}{Corollaire}[prop]
		\theoremstyle{plain}
		\theoremseparator{. ---}
	\newtheorem{exo}{Exercice}[chapter]
		\theoremstyle{nonumberplain}
	\newtheorem{exemple}{Exemple}
	\newtheorem{nota}{Notation}
	\newtheorem{rqe}{Remarque}
		\theorempreskip{0pt}
		\theoremindent2.5em
		\theoremsymbol{\scalebox{1.8}{\textbullet}}
	\newtheorem{preuve}{Preuve}

\RequirePackage{tikz}
	\usetikzlibrary{arrows}
	\usetikzlibrary{cd}
	\usetikzlibrary[patterns]

\usepackage{mathpartir}

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

% ---------- Divers ----------

%\RequirePackage{array}
%\RequirePackage{booktabs}
%	\setlength{\heavyrulewidth}{2pt}
%	\setlength{\aboverulesep}{5pt}
%	\setlength{\belowrulesep}{5pt}
%	\setlength{\belowbottomsep}{5pt}
\RequirePackage{csquotes}
%\RequirePackage{fancybox}
\RequirePackage{graphicx}
%\RequirePackage{lettrine}
\RequirePackage{lipsum}
%\RequirePackage{soul}
%\RequirePackage{shadow}
\RequirePackage{xcolor}
\RequirePackage{etoolbox}
\RequirePackage{xparse}
\RequirePackage{xspace}


% ---------- Métadonnées et références croisées ----------

% LIENS ET MÉTADONNÉES PDF
\RequirePackage{hyperref}
\definecolor{lien}{rgb}{0,0,0}
\hypersetup{colorlinks=true,
	allcolors= lien
	}

\usepackage{cleveref}
	\crefname{defi}{définition}{définitions}
	\crefname{lem}{lemme}{lemmes}
	
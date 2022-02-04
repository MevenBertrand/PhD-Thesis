\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{myarticle}
\LoadClass[twoside, a4paper]{article}

\RequirePackage{ifthen}

\newboolean{@fr} \setboolean{@fr}{false}
\DeclareOption{fr}{
	\setboolean{@fr}{true}
}

\newboolean{@en} \setboolean{@en}{false}
\DeclareOption{en}{
	\setboolean{@en}{true}
}

\ProcessOptions\relax

% Couleurs
% -------------------------------------------------------------

\RequirePackage{xcolor}

% Mise en page
%---------------------------------------------------------

\RequirePackage{indentfirst}

\RequirePackage{appendix}

\RequirePackage[a4paper, margin=2cm]{geometry}

%Floats
\RequirePackage{float}
\floatstyle{boxed} 
\restylefloat{figure}

\RequirePackage{placeins}

\RequirePackage[thmmarks, framed]{ntheorem}
\RequirePackage[ntheorem=true]{mdframed}

\definecolor{linkred}{rgb}{0.82, 0.1, 0.26}
\definecolor{linkgreen}{rgb}{0.0, 0.5, 0.0}

\RequirePackage[colorlinks, urlbordercolor= blue, urlcolor=blue, citebordercolor=linkgreen, citecolor=linkgreen, linkbordercolor=linkred, linkcolor=linkred, bookmarksopen=true]{hyperref}


% Définition des théorèmes
% ------------------------------------------------------

\if@fr
	\usepackage[french]{babel}

	\newcommand{\nomthm}{Th\'eor\`eme}
	\newcommand{\nomax}{Axiome}
	\newcommand{\nomprop}{Proposition}
	\newcommand{\nomcor}{Corollaire}
	\newcommand{\nomdf}{D\'efinition}
	\newcommand{\nomlem}{Lemme}
	\newcommand{\nomdem}{D\'emonstration}
	\newcommand{\nomeg}{Exemple}
	\newcommand{\nomrqe}{Remarque}
	\newcommand{\nomexo}{Exercice}
	\newcommand{\nomalg}{Algorithme}
	
	\def\chapterautorefname{Chapitre}
	\def\sectionautorefname{Section}
	\def\subsectionautorefname{Section}
\fi

\if@en
	\usepackage[english]{babel}
	
	\newcommand{\nomthm}{Theorem}
	\newcommand{\nomprop}{Proposition}
	\newcommand{\nomcor}{Corollary}
	\newcommand{\nomdf}{Definition}
	\newcommand{\nomlem}{Lemma}
	\newcommand{\nomdem}{Proof}
	\newcommand{\nomeg}{Example}
	\newcommand{\nomrqe}{Remark}
	\newcommand{\nomexo}{Exercice}
	\newcommand{\nomax}{Axiom}
	\newcommand{\nomalg}{Algorithm}
	
	\def\chapterautorefname{Chapter}
	\def\sectionautorefname{Section}
	\def\subsectionautorefname{Section}
\fi


\theorembodyfont{\normalfont}

\theoremstyle{break}

\newframedtheorem{thm}{\nomthm}
\newframedtheorem{prop}[thm]{\nomprop}
\newframedtheorem{ax}{\nomax}
\newtheorem{cor}[thm]{\nomcor}
\newtheorem{lem}[thm]{\nomlem}
\newframedtheorem{alg}{\nomalg}

\newframedtheorem{df}[thm]{\nomdf}
\newtheorem{eg}[thm]{\nomeg}
\newtheorem{rqe}[thm]{\nomrqe}
\newtheorem{exo}[thm]{\nomexo}

\theoremstyle{nonumberbreak}
\theorembodyfont{\small}

\newtheorem{dem}{\nomdem}

\endinput
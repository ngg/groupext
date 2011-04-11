\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\newcommand{\newargument}[1]{
	\expandafter\providecommand\csname @#1\endcsname{}
	\expandafter\providecommand\csname #1\endcsname{}
	\expandafter\renewcommand\csname @#1\endcsname{Missing #1}
	\expandafter\renewcommand\csname #1\endcsname[1]{\expandafter\renewcommand\csname @#1\endcsname{##1}}
}

\newargument{isfinal}
\isfinal{false}
\DeclareOption{final}{\isfinal{true}}

\newargument{isdvips}
\isdvips{false}
\DeclareOption{dvips}{\isdvips{true}}

\ProcessOptions\relax

\LoadClass[a4paper,twoside,12pt]{article}
\RequirePackage{ifthen}

\ifthenelse{\equal{\@isfinal}{true}}{
	\PassOptionsToPackage{disable}{todonotes}
}{

}

\ifthenelse{\equal{\@isdvips}{true}}{
	\PassOptionsToClass{dvips}{article}
	\PassOptionsToPackage{dvips}{geometry}
	\PassOptionsToPackage{dvips}{graphicx}
	\PassOptionsToPackage{dvips}{hyperref}
}{
	\PassOptionsToClass{pdftex}{article}
	\PassOptionsToPackage{pdftex}{geometry}
	\PassOptionsToPackage{pdftex}{hyperref}
	\PassOptionsToPackage{pdftex}{graphicx}
}

\def\magyarOptions{defaults=hu-min}
\RequirePackage[magyar]{babel}

\special{papersize=210mm,297mm}
\RequirePackage[utf8]{inputenc}
\RequirePackage[T1]{fontenc}
\RequirePackage{graphicx}
\ifthenelse{\equal{\@isdvips}{false}}{
	\RequirePackage{epstopdf}
}{}
\RequirePackage{ae}
\RequirePackage{aecompl}
\RequirePackage[a4paper,twoside,top=2.5cm,bottom=2.5cm,inner=3.5cm,outer=2.5cm]{geometry}
\RequirePackage[onehalfspacing]{setspace}
\RequirePackage{cite}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amsthm}
\RequirePackage{dsfont}
\RequirePackage[color=green]{todonotes}
\RequirePackage[unicode,pdfpagelayout=TwoPageRight,bookmarksopen]{hyperref}

\setcounter{secnumdepth}{3}
\renewcommand\thesection{\arabic{section}}
\renewcommand\thesubsection{\thesection.\arabic{subsection}}
\renewcommand\thesubsubsection{\thesubsection.\arabic{subsubsection}}
\numberwithin{equation}{subsection}
\renewcommand\theequation{\thesubsection.\arabic{equation}}

\newtheorem{theorem}{Tétel}[subsection]
\newtheorem{definition}[theorem]{Definíció}
\newtheorem{notation}[theorem]{Jelölés}
\newtheorem{statement}[theorem]{Állítás}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Következmény}
\newtheorem{remark}[theorem]{Megjegyzés}

\newargument{title}
\newargument{author}
\newargument{supervisor}
\newargument{supervisorrank}
\newargument{department}
\newargument{faculty}
\newargument{university}
\newargument{calltoarms}
\calltoarms{}
\newargument{placeanddate}


\renewcommand\maketitle{
	\begin{center}
	\textsc{\@university\\ \@faculty}
	\vspace{0.5cm}
	\hrule
	\vspace{3cm}
	{\large\@author}\\[1cm]
	{\Large\textsc{\@title}}\\[2cm]
	Szakdolgozat\\[4cm]
	Témavezető: \@supervisor, \@supervisorrank\\
	\@department
	\vfill
	\ifthenelse{\equal{\@calltoarms}{}}{}{
		\includegraphics[width=5cm]{\@calltoarms}\\
	}
	\@placeanddate
	\end{center}
	\thispagestyle{empty}
	\clearpage
	\mbox{}
	\thispagestyle{empty}
	\clearpage
}

\AtBeginDocument{
	\hypersetup{pdfinfo={
		Title={\@title},
		Author={\@author}
	}}
	\maketitle
	\renewcommand{\contentsname}{Tartalomjegyzék}
	\tableofcontents
	\addcontentsline{toc}{section}{\contentsname}
	\clearpage
}

\newargument{bibfile}
\bibfile{}
\newargument{bibstyle}
\bibstyle{amsalpha}

\AtEndDocument{
	\clearpage
	\ifthenelse{\equal{\@bibfile}{}}{}{
		\ifthenelse{\equal{\@isfinal}{false}}{
			\nocite{*}
		}{}
		\renewcommand{\refname}{Hivatkozások}
		\bibliographystyle{\@bibstyle}
		\addcontentsline{toc}{section}{\refname}
		\bibliography{\@bibfile}
		\clearpage
	}
	\ifthenelse{\equal{\@isfinal}{false}}{
		\todototoc
		\listoftodos
		\clearpage
	}{}
}

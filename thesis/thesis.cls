\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{thesis}

\newcommand{\newargument}[1]{
	\expandafter\providecommand\csname @#1\endcsname{}
	\expandafter\providecommand\csname #1\endcsname{}
	\expandafter\renewcommand\csname @#1\endcsname{Missing #1}
	\expandafter\renewcommand\csname #1\endcsname[1]{\expandafter\renewcommand\csname @#1\endcsname{##1}}
}

\RequirePackage{ifthen}
\newcommand{\ifargelse}[4]{\ifthenelse{\equal{\csname @#1\endcsname}{#2}}{#3}{#4}}
\newcommand{\ifarg}[3]{\ifargelse{#1}{#2}{#3}{}}
\newcommand{\ifargnot}[3]{\ifargelse{#1}{#2}{}{#3}}
\newcommand{\ifargtrueelse}[3]{\ifargelse{#1}{true}{#2}{#3}}
\newcommand{\ifargtrue}[2]{\ifargtrueelse{#1}{#2}{}}
\newcommand{\ifargfalse}[2]{\ifargtrueelse{#1}{}{#2}}

\newargument{isfinal}
\isfinal{false}
\DeclareOption{final}{\isfinal{true}}

\newargument{numberingin}
\numberingin{subsection}
\newargument{thenumberingin}
\thenumberingin{\thesubsection}
\DeclareOption{numbersection}{\numberingin{section}\thenumberingin{\thesection}}
\DeclareOption{numbersubsection}{\numberingin{subsection}\thenumberingin{\thesubsection}}
\DeclareOption{numbersubsubsection}{\numberingin{subsubsection}\thenumberingin{\thesubsubsection}}

\ProcessOptions\relax

\ifargtrue{isfinal}{
	\PassOptionsToPackage{disable}{todonotes}
}

\RequirePackage{ifpdf}
\ifpdf
	\PassOptionsToClass{pdftex}{article}
	\PassOptionsToPackage{pdftex}{geometry}
	\PassOptionsToPackage{pdftex}{hyperref}
	\PassOptionsToPackage{pdftex}{graphicx}
\else
	\PassOptionsToClass{dvips}{article}
	\PassOptionsToPackage{dvips}{geometry}
	\PassOptionsToPackage{dvips}{graphicx}
	\PassOptionsToPackage{dvips}{hyperref}
\fi

\LoadClass[a4paper,twoside,12pt]{article}

\def\magyarOptions{defaults=hu-min}
\RequirePackage[magyar]{babel}

\special{papersize=210mm,297mm}
\RequirePackage[utf8]{inputenc}
\RequirePackage[T1]{fontenc}
\RequirePackage{graphicx}
\ifpdf
	\RequirePackage{epstopdf}
\fi
\RequirePackage{ae}
\RequirePackage{aecompl}
\RequirePackage[a4paper,twoside,top=2.5cm,bottom=4cm,inner=3.5cm,outer=2.5cm,footskip=2cm]{geometry}
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
\numberwithin{equation}{\@numberingin}
\renewcommand\theequation{\@thenumberingin.\arabic{equation}}

\let\@oldcite\cite
\renewcommand\cite[1]{\ifthenelse{\equal{#1}{need}}{\todo{Hivatkozás hiányzik}}{\@oldcite{#1}}}

\newtheorem{theorem}{Tétel}[\@numberingin]
\newtheorem{definition}[theorem]{Definíció}
\newtheorem{notation}[theorem]{Jelölés}
\newtheorem{statement}[theorem]{Állítás}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Következmény}
\newtheorem{remark}[theorem]{Megjegyzés}

\newargument{title}
\newargument{author}
\newargument{degree}
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
	Szakdolgozat\\
	\@degree\\[4cm]
	Témavezető: \@supervisor, \@supervisorrank\\
	\@department
	\vfill
	\ifargnot{calltoarms}{}{
		\includegraphics[width=5cm]{\@calltoarms}\\
	}
	\@placeanddate
	\end{center}
	\thispagestyle{empty}
	\clearpage
	\phantomsection
	\mbox{}
	\thispagestyle{empty}
	\clearpage
	\phantomsection
}

\AtBeginDocument{
	\hypersetup{pdftitle={\@title},pdfauthor={\@author}}
	\addcontentsline{toc}{section}{Címlap}
	\maketitle
	\renewcommand{\contentsname}{Tartalomjegyzék}
	\tableofcontents
	\addcontentsline{toc}{section}{\contentsname}
	\clearpage
	\phantomsection
}

\newargument{bibfile}
\bibfile{}
\newargument{bibstyle}
\bibstyle{alpha}

\AtEndDocument{
	\clearpage
	\phantomsection
	\ifargnot{bibfile}{}{
		\ifargfalse{isfinal}{
			\nocite{*}
		}
		\renewcommand{\refname}{Hivatkozások}
		\bibliographystyle{\@bibstyle}
		\addcontentsline{toc}{section}{\refname}
		\bibliography{\@bibfile}
		\clearpage
		\phantomsection
	}
	\ifargfalse{isfinal}{
		\todototoc
		\listoftodos
		\clearpage
		\phantomsection
	}
}

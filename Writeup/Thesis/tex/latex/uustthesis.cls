\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{uustthesis}[2018/07/04 Utrecht University Software Technology Thesis Template]
%% We'll build on top of the 'book' class.
\LoadClass[oneside]{book}

%% Basic Commands

%% Necessary Packags
\RequirePackage{geometry}
\RequirePackage{fancyhdr}
\RequirePackage{xcolor}
\RequirePackage{ccaption}
\RequirePackage{graphicx}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{unicode-math}
\RequirePackage{cleveref}
\RequirePackage{catchfilebetweentags}
\RequirePackage[conor]{agda}

%% Declaring our Options

%% Paper sizes are handled by the geometry package.
\DeclareOption{a4paper}{\PassOptionsToClass{a4paper}{book}\geometry{a4paper}}
\DeclareOption{a5paper}{\passOptionsToClass{a5paper}{book}\geometry{a5paper}}

%% Here we can pass undeclared options to some class
%% or package
\DeclareOption*{%
  \PassOptionsToClass{\CurrentOption}{book}%
}
\ProcessOptions\relax 
%% This finishes the 'options' section

%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%
%% Our Commands %%
%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%

\newcommand{\HRule}{\rule{\linewidth}{0.5mm}} % Defines a new command for horizontal lines, change thickness here

%% Took from Dissertate @ https://github.com/suchow/Dissertate commit 58b4f
\newcommand{\dnormalspacing}{1.2}
\newcommand{\dcompressedspacing}{1.05}

% Block quote with compressed spacing
\let\oldquote\quote
\let\endoldquote\endquote
\renewenvironment{quote}
    {\begin{spacing}{\dcompressedspacing}\oldquote}
    {\endoldquote\end{spacing}}

% Itemize with compressed spacing
%\let\olditemize\itemize
%\let\endolditemize\enditemize
%\renewenvironment{itemize}
%    {\begin{spacing}{\dcompressedspacing}\olditemize}
%    {\endolditemize\end{spacing}}

% Enumerate with compressed spacing
%\let\oldenumerate\enumerate
%\let\endoldenumerate\endenumerate
%\renewenvironment{enumerate}
%   {\begin{spacing}{\dcompressedspacing}\oldenumerate}
%    {\endoldenumerate\end{spacing}}

%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%
%% Text Layout %%
%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%

%% Margins and Geomtry config
\geometry{lmargin=.20\textwidth}
\geometry{rmargin=.20\textwidth}
\geometry{tmargin=.25\textheight}
\geometry{twoside,bindingoffset=1cm}
\savegeometry{uustthesis-geometry}

% Headings and headers.
\RequirePackage{fancyhdr}
\RequirePackage[md, sc]{titlesec}
\setlength{\headheight}{15pt}
\pagestyle{plain}
\RequirePackage{titling}

% Front matter.
\setcounter{tocdepth}{1}
\usepackage[titles]{tocloft}
\usepackage[titletoc]{appendix}
\renewcommand{\cftsecleader}{\cftdotfill{\cftdotsep}}
\renewcommand{\cftchapfont}{\normalsize \scshape}
\renewcommand\listfigurename{Listing of figures}
\renewcommand\listtablename{Listing of tables}


%% Font Confiruation using unicode-math package
%% https://tex.stackexchange.com/questions/30049/how-to-select-math-font-in-document#30066
%%
%% WARNING: Fonts must be installed locally; to do so,
%%          run 'make fonts'
\defaultfontfeatures{Scale=MatchLowercase}

%% Choosing STIX Two as our font
%%
%% This also loads some fancier stylistic sets for \mathcal and stuff.
\setmathfont{STIX Two Math}[StylisticSet={1,2,8}, version=stix2_128]
\setmathfont{STIX Two Math}[version=stix2_128]
\setmainfont{Linux Libertine}
\mathversion{stix2_128}

%% Choosing XITS as our font
% \setmathfont{XITS Math}[version=xits]
% \setmainfont{XITS}
% \mathversion{xits}

%% Choosing Libertine as our font
% \setmainfont{Linux Libertine}

%% Choosing TeX Gyre Pagella as our font
%\setmathfont{TeX Gyre Pagella Math}[version=pagella]
%\setmainfont{TeX Gyre Pagella}
%\mathversion{pagella}

%% Fancy Chapter Headers
\RequirePackage{quotchap}
%% Hacking quotchap
\renewcommand*{\chapnumfont}{%
  \fontsize{100}{130}\selectfont% Default: 100/130
  \color{chaptergrey}%
}
\renewcommand*{\chapterheadstartvskip}{\vspace*{-4\baselineskip}}
\renewcommand*{\chapterheadendvskip}{\vspace{0.8\baselineskip}}

%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%
%%  Title Page  %%
%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%

%% Declare a supervisor variable for our title page.
\let\@supervisor\@empty
\newcommand{\supervisor}[1]{\gdef\@supervisor{#1}}

\renewcommand{\maketitle}{
%%%%%%%%%%%%%
%% Custom title page geometry
\newgeometry{left=3cm,right=3cm}
\thispagestyle{empty}
\begin{center}
%%%%%%%%%%%%%
%% Headings
  \begin{minipage}{0.25\textwidth}%
  \includegraphics[width=.8\textwidth]{img/logo.pdf}%
  \end{minipage}
  ~
  \begin{minipage}{0.7\textwidth}%
  \begin{flushleft}
  \textsc{\huge Universiteit Utrecht}\vskip 1.5em
  \textsc{\Large Faculty of Science}\vskip 0.5em
  \textsc{\large Dept. of Information and Computing Sciences}%
  \end{flushleft}
  \end{minipage}
%%%%%%%%%%%
%% Title
  \vfill
  \HRule\vskip 1.5em
  {\huge\bfseries \@title }
  \vskip 1em \HRule
  \vfill
%%%%%%%%%%
%% Author(s)
  \begin{minipage}{0.4\textwidth}
    \begin{flushleft}\large
    \textit{Author}\vskip .5em
    \@author
    \end{flushleft}
  \end{minipage}
  ~
  \begin{minipage}{0.4\textwidth}
  \begin{flushright}\large
  \textit{Supervisor}\vskip .5em
  \@supervisor
  \end{flushright}
  \end{minipage}
  \vfill\vfill\vfill
%%%%%%%%%%%%
%% Date
  {\large\@date} 
  \vfill\newpage
\end{center}
%%%%%%%%%%%%
%% Restore our previous geometry
\restoregeometry
}

%% End of title page

%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%
%% sectsty conf %%
%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%

% 
% \titleformat{\chapter}[block]%
% {\bfseries\Large\filleft}%
% {\Huge\color{gray}\thechapter}%
% {1em}
% {\hfill\Huge\scshape}%
% [\HRule]

\makeatletter
\@ifpackageloaded{stix}{%
}{%
  \DeclareFontEncoding{LS2}{}{\noaccents@}
  \DeclareFontSubstitution{LS2}{stix}{m}{n}
  \DeclareSymbolFont{stix@largesymbols}{LS2}{stixex}{m}{n}
  \SetSymbolFont{stix@largesymbols}{bold}{LS2}{stixex}{b}{n}
  \DeclareMathDelimiter{\lBrace}{\mathopen} {stix@largesymbols}{"E8}%
                                            {stix@largesymbols}{"0E}
  \DeclareMathDelimiter{\rBrace}{\mathclose}{stix@largesymbols}{"E9}%
                                            {stix@largesymbols}{"0F}
}
\makeatother

\usepackage{newunicodechar}
\newunicodechar{∷}{\ensuremath{∷}}
\newunicodechar{▻}{\ensuremath{▻}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{⦇}{\ensuremath{\llparenthesis}}
\newunicodechar{⦈}{\ensuremath{\rrparenthesis}}
\newunicodechar{≃}{\ensuremath{\simeq}}
\newunicodechar{𝓤}{\ensuremath{\mathcal{U}}}
\newunicodechar{≟}{\ensuremath{\overset{_?}{=}}}
\newunicodechar{⊎}{\ensuremath{\uplus}}
\newunicodechar{¬}{\ensuremath{\neg}}
\newunicodechar{⊥}{\ensuremath{\bot}}
\newunicodechar{𝔾}{\ensuremath{\mathbb{G}}}
\newunicodechar{ᵢ}{\ensuremath{_{i}}}
\newunicodechar{ᵣ}{\ensuremath{_{r}}}
\newunicodechar{⦃}{\ensuremath{\lBrace}}
\newunicodechar{⦄}{\ensuremath{\rBrace}}
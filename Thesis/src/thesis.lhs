\documentclass[10pt,a4paper,msc]{uustthesis}

\usepackage{lipsum}

\title{Testing A Large Title YAY}
\titleDUTCH{Same title in Dutch}

\author{Victor Cacciari Miraldo}

\promotor{Prof.dr. J.T. Jeuring}
\copromotor{Dr. W. Swierstra}

\NWOproject{nwo project name here}
\NWOgrantnumber{111.111.111}

\defensedate{hopefuly, in the future!}
\authorbirthdate{october 16, 1991}
\authorbirthplace{S\~{a}o Paulo, Brasil}

%include lhs2TeX.fmt
\begin{document}
\maketitle

%% Set up the front matter of our book
\frontmatter
\tableofcontents

\chapter{Declaration}
Thanks to family, supervisor, friends and hops!

\chapter{Abstract}
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.
Some amazing abstract should come here.

%% Starts the mainmatter
\mainmatter

\chapter{Introduction}
%include src/chap01.lhs

\chapter{Conclusion}
\input{src/chap02}

\appendix
\chapter{Some Formulas}

\backmatter
\listoffigures
\listoftables

\bibliographystyle{alpha}
\bibliography{references}

\end{document}



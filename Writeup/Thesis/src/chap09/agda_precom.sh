# cleanup
rm *.agdai
rm -rf ./latex/ 

# Compile code to .tex
agda --latex code.lagda

# apply post processing 
cd latex/
perl ../../../postprocess-latex.pl code.tex > code.processed 
mv code.processed code.tex 


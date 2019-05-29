{ pkgs ? import <nixpkgs> {} }:

let 
  fontsConf  = pkgs.makeFontsConf {
    fontDirectories = [ ./tex/latex/fonts ];
  };
  texlive = pkgs.texlive.combine {
    inherit (pkgs.texlive) 
      appendix
      ccaption 
      euenc 
      filehook 
      fontspec 
      graphics 
      lazylist
      polytable
      quotchap
      scheme-basic 
      stmaryrd 
      titlesec 
      titling 
      tocloft 
      unicode-math 
      xcolor 
      xetex 
      ;
  };
in
pkgs.stdenv.mkDerivation {
  name = "thesis";
  src = ./.;
  FONTCONFIG_FILE = "${fontsConf}";
  buildInputs = [ pkgs.haskellPackages.lhs2tex pkgs.fontconfig texlive ];
}

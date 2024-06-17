{ sources, lib, ocamlPackages }:

let
  patricia-tree = sources.patricia-tree;
in

ocamlPackages.buildDunePackage {
  strictDeps = true;
  pname = "patricia-tree";
  inherit (patricia-tree) version;

  minimalOCamlVersion = "4.08";
  duneVersion = "3";

  src = patricia-tree;

  meta = with lib; {
    inherit (patricia-tree) homepage description;
  };
}

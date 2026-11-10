{ sources, lib, buildDunePackage }:

buildDunePackage {
  pname = "weak_hashset";
  version = "dev";

  patches = [ ./dune-project.patch ];

  minimalOCamlVersion = "5.1";
  src = sources.weak_hashset;
}

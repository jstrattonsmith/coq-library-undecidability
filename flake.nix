{
  description = "A Coq/Rocq Library of Undecidability Proofs";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/c5296fdd05cfa2c187990dd909864da9658df755";
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };

        packages.default = pkgs.coqPackages.coq-library-undecidability;

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
            pkgs.rocqPackages.vsrocq-language-server
          ];
          inputsFrom = [ self'.packages.default ];
        };
      };
      flake = {
        overlays.default = final: prev: {
          coqPackages = prev.coqPackages.overrideScope (final: prev: {
            coq-library-undecidability = prev.mkCoqDerivation {
              pname = "coq-library-undecidability";
              version = ./.;
              # L/Tactics/Extract.v needs the equations OCaml findlib
              # plugin, and several L/* files need MetaRocq's Template
              # monad machinery.
              mlPlugin = true;
              propagatedBuildInputs = [
                final.coq
                final.equations
                final.metarocq-template-rocq
                final.metarocq-utils
                final.metarocq-common
                final.metarocq-pcuic
                final.metarocq-template-pcuic
                final.metarocq-safechecker
                final.metarocq-erasure
              ];
            };
          });
        };
      };
    };
}

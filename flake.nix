{
  description = "A very basic flake";

  ###################################################
  inputs =
  {
    # base imports
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    # determi
    agda-driver.url = "github:determi-io/agda-driver";

  };

  ###################################################
  outputs = { self, nixpkgs, flake-utils, agda-driver }:
  (
    let mkOutputs = system:
    (
      let pkgs = import nixpkgs { inherit system; };
          agda-driver-bin = "${agda-driver.defaultPackage.${system}}/bin/agda-driver";
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [ pkgs.agda pkgs.stack ];
          driver = agda-driver-bin;
          myoutpath = self.outPath;

          # DETERMI_NIX_AGDA_PATH = "${agda.outputs.packages.x86_64-linux.Agda}/bin/agda";
        };

        packages.default = derivation {
          name = "determi-io-agda-stdlib";
          builder = "${pkgs.bash}/bin/bash";
          args = [ ./builder.sh ];
          STDLIB_ROOT = ./.;
          CP = "${pkgs.coreutils}/bin/cp";
          MKDIR = "${pkgs.coreutils}/bin/mkdir";
          LS = "${pkgs.coreutils}/bin/ls";
          ECHO = "${pkgs.coreutils}/bin/echo";
          PWD = "${pkgs.coreutils}/bin/pwd";
          CHMOD = "${pkgs.coreutils}/bin/chmod";
          STACK = "${pkgs.stack}/bin/stack";
          AGDA = "${pkgs.agda}/bin/agda";
          LOCALE_ARCHIVE = "${pkgs.glibcLocalesUtf8}/lib/locale/locale-archive";
          LOCALE = "${pkgs.locale}/bin/locale";
          LC_ALL= "en_US.utf8";
          inherit system;
          src = ./.;
        };

        # pkgs.stdenv.mkDerivation {
        #   inherit system;
        #   name = "simple";
        #   builder = "${pkgs.bash}/bin/bash";
        #   args = [ ./simple_builder.sh ];
        # };

      }
    );

    in flake-utils.lib.eachDefaultSystem mkOutputs
  );

}



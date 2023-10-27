{
  description = "A very basic flake";

  ###################################################
  inputs =
  {
    # base imports
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    # agda
    # NOTE: We cannot use the nixpkgs.agda because it has
    # ghc as runtime dependency, making the resulting closure
    # very large!
    agda =
    {
      type = "github";
      owner = "determi-io";
      repo = "agda-only-agda";
    };

    # determi
    # agda-driver.url = "github:determi-io/agda-driver";
  };

  ###################################################
  outputs = { self, nixpkgs, flake-utils, agda }:
  (
    let mkOutputs = system:
    (
      let pkgs = import nixpkgs { inherit system; };
          # agda-driver-bin = "${agda-driver.defaultPackage.${system}}/bin/agda-driver";
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [  ];
          # driver = agda-driver-bin;
          myoutpath = self.outPath;

          AGDA = "${agda.outputs.packages.x86_64-linux.determi-io-agda-only-agda}/bin/agda";
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
          AGDA = "${agda.outputs.packages.x86_64-linux.default}/bin/agda";
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



{
  description = "A Flake for Applying Grackle to gokv";

  inputs = {
    nixpkgs.url = "nixpkgs";
  };

  outputs = {nixpkgs, ...}: let
    system = "x86_64-linux";
  in {
    devShells."${system}".default = let
      pkgs = import nixpkgs {
        inherit system;
      };
      grackle = pkgs.buildGoModule {
        name = "grackle";
        src = pkgs.fetchFromGitHub {
          owner = "mjschwenne";
          repo = "grackle";
          rev = "3a83c3b22f163da77d75bfdb3923f007af2ad515";
          sha256 = "1bl8lx50qhl6yczjnwfwywx29nvinr20v2zjdc2zjqi8kcls7kqr";
        };
        vendorHash = "sha256-c9+npmcdynfqSnxEZSdubVeN8Y3eYAwjya52vTJayY0=";
        checkPhase = false;
      };
      goose = pkgs.buildGoModule {
        name = "goose";
        src = pkgs.fetchFromGitHub {
          owner = "goose-lang";
          repo = "goose";
          rev = "67cf95ebfc80e80ddc40b0518e6d761cde44977c";
          sha256 = "16040c4frxn9dk3xmajzg4jb7fi7q39hasfp94rpnphmpr4hvr51";
        };
        vendorHash = "sha256-HCJ8v3TSv4UrkOsRuENWVz5Z7zQ1UsOygx0Mo7MELzY=";
      };
    in
      pkgs.mkShell {
        packages = [
          # coq deps
          pkgs.coq

          pkgs.go
          grackle
          goose
          pkgs.protobuf

          # nix helper
          # Should be able to update goose and grackle with `update-nix-fetchgit flake.nix`
          pkgs.update-nix-fetchgit
          pkgs.nix-prefetch-git
          pkgs.nix-prefetch
        ];

        shellHook = ''
        '';
      };
  };
}

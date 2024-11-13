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
          rev = "50fb62a4d9363e09c25e997b452eac4af844b5cd";
          sha256 = "16vgpxdkg2686r0m2dqlxm5czxgf07j0myxixsqc84k1z90kivy6";
        };
        vendorHash = "sha256-Wk2v0HSAkrzxHJvCfbw6xOn0OQ1xukvYjDxk3c2LmH8=";
        checkPhase = false;
      };
      goose = pkgs.buildGoModule {
        name = "goose";
        src = pkgs.fetchFromGitHub {
          owner = "goose-lang";
          repo = "goose";
          rev = "8352f2a82040a814b60e0dd9ac75f09cec3dd619";
          sha256 = "0as9cw8v6bxwv2100db63nk8h2mk3330c8kmdlk3kjzlkvy1bdwf";
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

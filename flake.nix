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
          rev = "275fce5626d662527ff987ad61aad61044019fa6";
          sha256 = "16iw5hqg2hd12mc62wqv5hxqb8jwymbnhyy16zsza0limhmr0aya";
        };
        vendorHash = "sha256-Wk2v0HSAkrzxHJvCfbw6xOn0OQ1xukvYjDxk3c2LmH8=";
        checkPhase = false;
      };
      goose = pkgs.buildGoModule {
        name = "goose";
        src = pkgs.fetchFromGitHub {
          owner = "goose-lang";
          repo = "goose";
          rev = "8d13c771b9a80957089f7c5b0ee2ccf58e5eb06f";
          sha256 = "1fbqs75ya4as3my2knkaq4m0crdh3n004grw5g5iczvb5h5k06lz";
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

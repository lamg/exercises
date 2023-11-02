let
 unstable = import (fetchTarball https://nixos.org/channels/nixos-unstable/nixexprs.tar.xz) { };
 ocamlPkgs = unstable.ocamlPackages;
 ppx_yojson_conv = unstable.callPackage ./external_packages/ppx_yojson_conv.nix {pkgs=unstable;} ;
in
unstable.mkShell {
  # build tools
  nativeBuildInputs = with ocamlPkgs; [ ocaml findlib dune_3 merlin ocaml-lsp ffmpeg] ++
                                      [unstable.ocamlformat unstable.emacs28Packages.merlin
                                       unstable.emacs28Packages.tuareg unstable.emacs
                                       unstable.opam unstable.ocaml unstable.emacs28Packages.ripgrep
                                       unstable.ripgrep unstable.emacs28Packages.vterm

                                      ];
  # dependencies
  buildInputs = with ocamlPkgs; [ core ppx_deriving
                                  yojson
                                  ppxlib ppx_deriving yojson
                                  ppx_yojson_conv_lib alcotest ppx_yojson_conv ];
}

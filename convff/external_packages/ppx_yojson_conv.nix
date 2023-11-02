{pkgs}:
pkgs.ocamlPackages.buildDunePackage rec {
  pname = "ppx_yojson_conv";
  version = "0.14";
  useDune2 = true;

  minimalOCamlVersion = "4.08";

  src = pkgs.fetchFromGitHub {
    owner  = "janestreet";
    repo   = pname;
    rev = "v${version}";
    sha256 = "sha256-qZy8TzTnPUOkFwWThTDqN4tvaUCLA4ro6MBqhlzUxPw=";
  };

  buildInputs = [ pkgs.ocamlPackages.ppx_js_style pkgs.ocamlPackages.ppx_yojson_conv_lib
                  pkgs.ocamlPackages.ppxlib pkgs.ocamlPackages.base
                ];

  meta = {
    homepage = "https://github.com/janestreet/ppx_yojson_conv";
    description = "Part of the Jane Street's PPX rewriters collection.";
    maintainers = with pkgs.lib.maintainers; [ maintainers.marsam ];
    license = pkgs.lib.licenses.mit;
  };
}

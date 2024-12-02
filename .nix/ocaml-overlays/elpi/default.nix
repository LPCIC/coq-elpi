{ lib
, buildDunePackage, camlp5
, ocaml
, menhir, menhirLib
, atdgen
, stdlib-shims
, re, perl, ncurses
, ppxlib, ppx_deriving
, coqPackages
, version ? "2.0.3"
}:

let p5 = camlp5; in
let camlp5 = p5.override { legacy = true; }; in

let fetched = coqPackages.metaFetch ({
    release."2.0.3".sha256 = "sha256-t2z0sWPiFgp6LuR6CsH/Zk9qfxW+3QjjFcYrB6qSPgc=";
    release."1.20.0".sha256 = "sha256-lctZAIQgOg5d+LfILtWsBVcsemV3zTZYfJfDlCxHtcA=";
    release."1.19.2".sha256 = "sha256-dBj5Ek7PWq/8Btq/dggJUqa8cUtfvbi6EWo/lJEDOU4=";
    release."1.18.1".sha256 = "sha256-rrIv/mVC0Ez3nU7fpnzwduIC3tI6l73DjgAbv1gd2v0=";
    release."1.17.0".sha256 = "sha256-J8FJBeaB+2HtHjrkgNzOZJngZ2AcYU+npL9Y1HNPnzo=";
    release."1.15.2".sha256 = "sha256-+sQYQiN3n+dlzXzi5opOjhkJZqpkNwlHZcUjaUM6+xQ=";
    release."1.15.0".sha256 = "sha256-vpQzbkDqJPCmaBmXcBnzlWGS7djW9wWv8xslkIlXgP0=";
    releaseRev = v: "v${v}";
    releaseArtifact = v: if lib.versionAtLeast v "1.13.8"
      then "elpi-${v}.tbz"
      else "elpi-v${v}.tbz";
    location = { domain = "github.com"; owner = "LPCIC"; repo = "elpi"; };
  }) version;
in
buildDunePackage {
  pname = "elpi";
  inherit (fetched) version src;

  patches = lib.optional (version == "1.16.5")
    ./atd_2_10.patch;

  minimalOCamlVersion = "4.07";

  # atdgen is both a library and executable
  nativeBuildInputs = [ perl ]
  ++ [ menhir ]
  ++ lib.optional (lib.versionAtLeast version "1.16" || version == "dev") atdgen;
  buildInputs = [ ncurses ]
  ++ lib.optional (lib.versionAtLeast version "1.16" || version == "dev") atdgen;

  propagatedBuildInputs = [ re stdlib-shims menhirLib ppxlib ppx_deriving ];

  meta = with lib; {
    description = "Embeddable λProlog Interpreter";
    license = licenses.lgpl21Plus;
    maintainers = [ maintainers.vbgl ];
    homepage = "https://github.com/LPCIC/elpi";
  };

  postPatch = ''
    substituteInPlace elpi_REPL.ml --replace-warn "tput cols" "${ncurses}/bin/tput cols"
  '';
}

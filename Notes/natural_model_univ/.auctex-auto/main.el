(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "a4paper" "11pt")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("xy" "cmtip" "all") ("parskip" "parfill")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "href")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "prooftree"
    "groupoid_model"
    "article"
    "art11"
    "amsthm"
    "amsmath"
    "amssymb"
    "stmaryrd"
    "enumerate"
    "a4"
    "array"
    "geometry"
    "url"
    "xy"
    "hyperref"
    "cleveref"
    "parskip"
    "tikz"
    "tikz-cd"
    "float")
   (TeX-add-symbols
    '("disp" 1)
    '("psh" 1)
    "defeq"
    "iso"
    "equi"
    "retequi"
    "op"
    "Id"
    "Nat"
    "co"
    "catC"
    "tcat"
    "yo"
    "pshC"
    "Type"
    "Term"
    "tp"
    "var"
    "Prop"
    "U"
    "E"
    "El"
    "set"
    "Set"
    "cat"
    "Cat"
    "ptCat"
    "grpd"
    "ptgrpd"
    "Pshgrpd"
    "PshCat"
    "al"
    "be"
    "ga"
    "de"
    "ep"
    "io"
    "ka"
    "la"
    "om"
    "si"
    "Ga"
    "De"
    "Th"
    "La"
    "Si"
    "Om")
   (LaTeX-add-environments
    "comment")
   (LaTeX-add-bibliographies
    "refs.bib")
   (LaTeX-add-amsthm-newtheorems
    "theorem"
    "prop"
    "obs"
    "lemma"
    "cor"
    "applemma"
    "defn"
    "rmk"
    "eg"
    "ex"))
 :latex)


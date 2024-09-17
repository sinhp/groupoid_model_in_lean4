#let template(doc) = [
  // Numbering and styling for headings
  #set heading(numbering: "1.")
  #show heading.where(level: 3): set heading(outlined: false)
  #show heading.where(level: 4): set heading(outlined: false)
  #show heading: it => {
    if it.level < 3 { it }
    else {
      if it.numbering != none [
        #counter(heading).display("1.") #it.body.
      ] else [
        #it.body.
      ]
    }
  }

  // Don't number equations
  #set math.equation(numbering: none)

  // Improve behaviour of some math symbols
  #show math.equation: it => {
    show sym.arrow.t: math.class.with("unary")
    show sym.arrow.b: math.class.with("unary")
    show sym.arrow.r.double: math.class.with("binary")
    show sym.bot: math.class.with("normal")
    show sym.tack: math.scripts
    show sym.arrow.r: math.scripts
    show sym.arrow.r.twohead: math.scripts
    show sym.eq.triple: math.scripts
    show sym.arrow.r.long: math.scripts
    show sym.eq: math.scripts
    it
  }

  #doc
]

// A nice box
#let gbox(content) = box(stroke: black, inset: 6pt, baseline: 6pt, content)

#let hott0 = $"HoTT"_0$

#let sp = h(.3em)

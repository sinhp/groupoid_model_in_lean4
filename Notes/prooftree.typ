#let prooftree(
  spacing: (
    horizontal: 1em,
    vertical: 0.5em,
    lateral: 0.5em,
  ),
  label: (
    // TODO: split offset into horizontal and vertical
    offset: -0.1em,
    side: right,
    padding: 0.2em,
  ),
  line-stroke: 0.5pt,
  ..rules
) = {
  // Check the types of the parameters.
  assert(
    type(spacing) == "dictionary",
    message: "The value `" + repr(spacing) + "` of the `spacing` argument was expected"
      + "to have type `dictionary` but instead had type `" + type(spacing) + "`."
  )
  assert(
    type(label) == "dictionary",
    message: "The value `" + repr(label) + "` of the `label` argument was expected"
      + "to have type `dictionary` but instead had type `" + type(label) + "`."
  )
  assert(
    type(line-stroke) == "length",
    message: "The value `" + repr(line-stroke) + "` of the `line-stroke` argument was expected"
      + "to have type `length` but instead had type `" + type(line-stroke) + "`."
)

  // Check validity of `spacing`'s keys.
  for (key, value) in spacing {
    if key not in ("horizontal", "vertical", "lateral", "h", "v", "l") {
      panic("The key `" + key + "` in the `spacing` argument `" + repr(spacing) + "` was not expected.")
    }
    if type(value) != "length" {
      panic(
        "The value `" + repr(value) + "` of the key `" + key + "` in the `spacing` argument `" + repr(spacing)
        + "` was expected to have type `length` but instead had type `" + type(value) + "`."
      )
    }
  }

  // Check exclusivity of `spacing`'s keys.
  let mutually_exclusive(key1, key2, keys) = {
    assert(
      key1 not in keys or key2 not in keys,
      message: "The keys `" + key1 + "` and `" + key2 + "` in the `spacing` argument `"
        + repr(spacing) + "` are mutually exclusive."
    )
  }
  mutually_exclusive("horizontal", "h", spacing.keys())
  mutually_exclusive("vertical", "v", spacing.keys())
  mutually_exclusive("lateral", "l", spacing.keys())

  // Check validity of `label`'s keys.
  let expected = ("offset": "length", "side": "alignment", "padding": "length")
  for (key, value) in label {
    if key not in expected {
      panic("The key `" + key + "` in the `label` argument `" + repr(label) + "` was not expected.")
    }
    if type(value) != expected.at(key) {
      panic(
        "The value `" + repr(value) + "` of the key `" + key + "` in the `label` argument `" + repr(label)
        + "` was expected to have type `" + type.at(key) + "` but instead had type `" + type(value) + "`."
      )
    }
  }
  if "side" in label {
    assert(
      label.side == left or label.side == right,
      message: "The value for the key `side` in the argument `label` can only be either "
        + "`left` (default) or `right`, but instead was `" + repr(label.side) + "`."
    )
  }

  // Check basic validity of `rules`.
  if rules.pos().len() == 0 {
    panic("The `rules` argument cannot be empty.")
  }

  let settings = (
    spacing: (
      horizontal: spacing.at("horizontal", default: spacing.at("h", default: 1.5em)),
      vertical: spacing.at("vertical", default: spacing.at("v", default: 0.5em)),
      lateral: spacing.at("lateral", default: spacing.at("l", default: 0.5em)),
    ),
    label: (
      offset: label.at("offset", default: -0.1em),
      side: label.at("side", default: left),
      padding: label.at("padding", default: 0.2em),
    ),
    line-stroke: line-stroke,
  )

  // Draw the rules in a stack-based evaluation order.
  style(styles => {
    let stack = ()

    for rule in rules.pos() {
      let to_pop = rule.__prooftree_to_pop
      let rule_func = rule.__prooftree_rule_func

      assert(
        to_pop <= stack.len(),
        message: "The rule `" + repr(rule.__prooftree_raw) + "` was expecting at least "
          + str(to_pop) + " rules in the stack, but only " + str(stack.len()) + " were present."
      )

      let elem = rule_func(
        settings,
        styles,
        stack.slice(stack.len() - to_pop)
      )

      stack = stack.slice(0, stack.len() - to_pop)
      stack.push(elem)
    }

    assert(
      stack.len() == 1,
      message: "Some rule remained unmatched: " + str(stack.len()) + " roots were found but only 1 was expected."
    )

    set align(start)
    set box(inset: 0pt, outset: 0pt)

    stack.pop().body
  })
}

#let axiom(label: none, body) = {
  // Check the type of `label`.
  assert(
    type(label) in ("string", "content", "none"),
    message: "The type of the `label` argument `" + repr(label) + "` was expected to be "
     + "`none`, `string` or `content` but was instead `" + type(label) + "`."
  )

  // TODO: allow the label to be aligned on left, right or center (default and current).

  (
    __prooftree_raw: body,
    __prooftree_to_pop: 0,
    __prooftree_rule_func: (settings, styles, children) => {
      let body = box(body, inset: (x: settings.spacing.lateral))
      // let body = body
      if label != none {
        // Labels stack on top of axioms
        body = stack(
          dir: ttb,
          spacing: 1.5 * settings.spacing.vertical,
          align(center, label),
          body
        )
      }

      return (
        body: body,
        label_wleft: 0pt,
        label_wright: 0pt,
        wleft: 0pt,
        wright: 0pt,
      )
    }
  )
}

#let rule(
  n: 1,
  label: none,
  root
) = {
  // Check validity of the `n` parameter
  assert(
    type(n) == "integer",
    message: "The type of the `n` argument `" + repr(n) + "` was expected to be "
     + "`integer` but was instead `" + type(n) + "`."
  )

  // Check the type of `label`.
  assert(
    type(label) in ("string", "dictionary", "content", "none"),
    message: "The type of the `label` argument `" + repr(label) + "` was expected to be "
     + "`none`, `string`, `content` or `dictionary` but was instead `" + type(label) + "`."
  )
  // If the type of `label` was string then it's good, otherwise we need to check its keys.
  if type(label) == "dictionary" {
    for (key, value) in label {
      // TODO: maybe consider allowing `top`, `top-left` and `top-right` if `rule(n: 0)` gets changed.
      if key not in ("left", "right") {
        panic("The key `" + key + "` in the `label` argument `" + repr(label) + "` was not expected.")
      }
      if type(value) not in ("string", "content") {
        panic(
          "The value `" + repr(value) + "` of the key `" + key + "` in the `label` argument `" + repr(label)
          + "` was expected to have type `string` or `content` but instead had type `" + type(value) + "`."
        )
      }
    }
  }

  (
    __prooftree_raw: root,
    __prooftree_to_pop: n,
    __prooftree_rule_func: (settings, styles, children) => {
      let width(it) = measure(it, styles).width
      let height(it) = measure(it, styles).height
      let maxl(..lengths) = width(
        for length in lengths.pos() {
          line(length: length)
        }
      )
      let gtl(l1, l2) = maxl(l1, l2) != l2
      let minl(l1, l2) = if gtl(l1, l2) { l2 } else { l1 }

      let root = [ #h(settings.spacing.lateral) #root #h(settings.spacing.lateral) ]

      // Get some values from the children, or 0pt if n == 0
      let (
        children_wleft,
        children_label_wleft,
        children_wright,
        children_label_wright
      ) = (0pt, 0pt, 0pt, 0pt)
      if n != 0 {
        children_wleft = children.first().wleft
        children_label_wleft = children.first().label_wleft
        children_wright = children.last().wright
        children_label_wright = children.last().label_wright
      }

      // Map the children to a single block
      let branches = children.map(c => box(c.body)).join(h(settings.spacing.horizontal))

      // Calculate the offsets of the "inner" branches, i.e. ignoring branches' labels
      let wbranches_nolabel = width(branches) - children_label_wleft - children_label_wright
      let ibranches_offset = maxl(0pt, width(root) - wbranches_nolabel) / 2

      // Compute the start, end and length of the line to satisfy the "inner" branches
      let ib_line_start = ibranches_offset + children_wleft
      let ib_line_end = ibranches_offset + wbranches_nolabel - children_wright
      let ib_line_len = ib_line_end - ib_line_start

      // Pad the line length to satisfy the root too
      let line_len = maxl(ib_line_len, width(root))

      // Adjust the line start to account for the root padding
      let line_start = if gtl(ib_line_len, width(root)) {
        // No root padding
        ib_line_start
      } else if gtl(width(root), wbranches_nolabel) {
        // The "inner" branches are too tight
        0pt
      } else {
        // Weird, situation, we have `wbranches_nolabel > width(root) > ib_line_len`
        // The line should be adjusted so that it fits kinda in the middle
        // TODO: maybe this should also consider labels?
        let min_left = maxl(0pt, ib_line_end - line_len)
        let max_right = minl(maxl(wbranches_nolabel, width(root)), ib_line_start + line_len)
        (max_right + min_left) / 2 - line_len / 2
      }

      // Finish computing the offsets by considering the ignored left branches label
      let branches_offset = maxl(0pt, ibranches_offset - children_label_wleft)
      let line_start = line_start + (branches_offset + children_label_wleft - ibranches_offset)
      let root_offset = line_start + (line_len - width(root)) / 2

      // Compute body without the label.
      // This is needed later to calculate the sizes when placing the new labels.
      let body_nolabel = stack(
        dir: ttb,
        spacing: settings.spacing.vertical,
        box(inset: (left: branches_offset), branches),
        line(start: (line_start, 0pt), length: line_len, stroke: settings.line-stroke),
        box(inset: (left: root_offset), root),
      )

      // Normalize label given the default value in the `prooftree` function.
      let label = label
      if type(label) == "none" {
        label = (
          left: none,
          right: none
        )
      }
      if type(label) in ("string", "content") {
        label = (
          left: if settings.label.side == left { label } else { none },
          right: if settings.label.side == right { label } else { none }
        )
      }
      label = (
        left: label.at("left", default: none),
        right: label.at("right", default: none),
      )

      // Pad the labels to separate them from the rule
      let left_label = box(inset: (right: settings.label.padding), label.left)
      let right_label = box(inset: (left: settings.label.padding), label.right)

      // Compute extra space the left label might need
      let new_left_space = maxl(0pt, width(left_label) - line_start)
      let left_label_width_offset = maxl(0pt, line_start - width(left_label))

      // Compute the width offset of the right label
      let right_label_width_offset = new_left_space + line_start + line_len

      // Compute the final width
      let final_width = maxl(
        right_label_width_offset + width(right_label),
        new_left_space + width(body_nolabel)
      )

      // Place the label on top of the rest.
      // Note that this needs to fix the final dimensions in order to use `place`.
      let body = box(width: final_width, height: height(body_nolabel))[
        #set block(spacing: 0pt)
        #box(inset: (left: new_left_space), body_nolabel)
        #place(
          bottom + left,
          dx: left_label_width_offset,
          dy: settings.label.offset,
          box(height: 2 * (height(root) + settings.spacing.vertical), align(horizon, left_label))
        )
        #place(
          bottom + left,
          dx: right_label_width_offset,
          dy: settings.label.offset,
          box(height: 2 * (height(root) + settings.spacing.vertical), align(horizon, right_label))
        )
      ]

      // Compute the final sizes for the next rule
      let label_wleft = minl(
        new_left_space + branches_offset + children_label_wleft,
        left_label_width_offset + width(left_label)
      )
      let label_wright = minl(
        children_label_wright + (final_width - branches_offset - width(branches)),
        final_width - right_label_width_offset
      )
      let wleft = (new_left_space + root_offset) - label_wleft
      let wright = width(body) - new_left_space - root_offset - width(root) - label_wright

      (
        body: body,
        label_wleft: label_wleft,
        label_wright: label_wright,
        wleft: wleft,
        wright: wright,
      )
    }
  )
}

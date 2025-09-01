import json
from pathlib import Path

import math
from statistics import mean  # kept imported in case you later need it; safe to remove if unused


def load_ndjson(path):
    """
    Load an NDJSON (newline-delimited JSON) file.
    Returns a list of dicts, one per line.
    """
    data = []
    with open(path, "r", encoding="utf-8") as f:
        for lineno, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
                data.append(obj)
            except json.JSONDecodeError as e:
                raise ValueError(f"JSON parse error: {path}, line {lineno}: {e}")
    return data


def index_by_name(rows, required_fields=None, prefer="first"):
    """
    Index a list of dicts by 'name'.
    Duplicate handling:
      - prefer="first": keep the first occurrence
      - prefer="last":  keep the last occurrence
      - prefer="error": raise an error on duplicates
    Rows missing any required_fields are skipped.
    """
    if required_fields is None:
        required_fields = []
    out = {}
    for i, r in enumerate(rows):
        name = r.get("name")
        if name is None:
            # Skip rows without 'name'
            continue
        if any(k not in r for k in required_fields):
            # Skip rows missing required fields
            continue
        if name in out:
            if prefer == "first":
                continue
            elif prefer == "last":
                out[name] = r
            elif prefer == "error":
                raise ValueError(f"Duplicate name detected: {name}")
        else:
            out[name] = r
    return out


def make_scatter(xs_us, ys_us, out_svg_path, title="t_rkernel vs t_kernel",
                 log=False, xlabel="t_kernel (us)", ylabel="t_rkernel (us)"):
    """
    Create a scatter plot and save it as SVG.
    xs_us: list of x-values in microseconds
    ys_us: list of y-values in microseconds
    """
    import matplotlib
    matplotlib.use("Agg")  # Use a non-GUI backend suitable for servers/CI
    import matplotlib.pyplot as plt

    fig, ax = plt.subplots(figsize=(7, 5), dpi=120)

    ax.scatter(xs_us, ys_us, s=20, c="#1f77b4", alpha=0.75, edgecolors="none")

    ax.set_title(title)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)

    # Fixed axis limits (in microseconds)
    ax.set_xlim(-5, 100)
    ax.set_ylim(-100, 2000)

    if log:
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.grid(True, which="both", linestyle="--", alpha=0.3)
    else:
        ax.grid(True, linestyle="--", alpha=0.3)

    Path(str(out_svg_path)).parent.mkdir(parents=True, exist_ok=True)
    fig.tight_layout()
    fig.savefig(str(out_svg_path), format="svg")
    plt.close(fig)


def main():
    # Input file paths (NDJSON, values in nanoseconds)
    kernel_path = "sampletimes_kernel.json"
    rkernel_path = "sampletimes_rkernel.json"

    # Load data
    kernel_rows = load_ndjson(kernel_path)
    rkernel_rows = load_ndjson(rkernel_path)

    # Index rows by name, ensuring required fields exist
    kernel_by_name = index_by_name(kernel_rows, required_fields=["t_kernel", "name"], prefer="first")
    rkernel_by_name = index_by_name(rkernel_rows, required_fields=["t_rkernel", "name"], prefer="first")

    # Intersect names present in both datasets
    common_names = sorted(set(kernel_by_name.keys()) & set(rkernel_by_name.keys()))

    xs_ns = []  # x values in ns
    ys_ns = []  # y values in ns
    skipped_zero = 0
    skipped_missing = 0

    for name in common_names:
        t_kernel = kernel_by_name[name].get("t_kernel")
        t_rkernel = rkernel_by_name[name].get("t_rkernel")

        # Validate presence
        if t_kernel is None or t_rkernel is None:
            skipped_missing += 1
            continue
        # Skip zero denominators if ratios were to be computed (kept for data hygiene)
        if t_kernel == 0:
            skipped_zero += 1
            continue

        xs_ns.append(t_kernel)
        ys_ns.append(t_rkernel)

    if skipped_zero:
        print(f"Skipped entries with t_kernel == 0: {skipped_zero}")
    if skipped_missing:
        print(f"Skipped entries missing required fields: {skipped_missing}")

    if not xs_ns or not ys_ns:
        print("No data to plot.")
        return

    # Unit conversion: ns -> us
    ns_per_us = 1e3
    xs_us = [x / ns_per_us for x in xs_ns]
    ys_us = [y / ns_per_us for y in ys_ns]

    # Plot (x: us, y: us)
    make_scatter(
        xs_us,
        ys_us,
        "scatter_graph.svg",
        title="t_rkernel vs t_kernel",
        log=False,
        xlabel="t_kernel (us)",
        ylabel="t_rkernel (us)",
    )
    print("Scatter plot saved to: scatter_graph.svg (x and y in microseconds)")


if __name__ == "__main__":
    main()

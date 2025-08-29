import json
from pathlib import Path
from statistics import mean

def load_ndjson(path):
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
    Index a list of dicts by 'name'. For duplicate names:
      - prefer="first": keep the first occurrence
      - prefer="last":  keep the last occurrence
      - prefer="error": raise an error on duplicates
    Optionally ensure required_fields exist; rows missing them are skipped.
    """
    if required_fields is None:
        required_fields = []
    out = {}
    for i, r in enumerate(rows):
        name = r.get("name")
        if name is None:
            # Skip rows without a 'name'
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

def main(
    kernel_path="sampletimes_kernel.json",
    rkernel_path="sampletimes_rkernel.json",
    prefer="first",
    show_details=False,
):
    # Load files
    kernel_rows = load_ndjson(kernel_path)
    rkernel_rows = load_ndjson(rkernel_path)

    # Index by 'name'
    kernel_by_name = index_by_name(kernel_rows, required_fields=["t_kernel", "name"], prefer=prefer)
    rkernel_by_name = index_by_name(rkernel_rows, required_fields=["t_rkernel", "name"], prefer=prefer)

    # Find common names
    common_names = sorted(set(kernel_by_name.keys()) & set(rkernel_by_name.keys()))

    ratios = []
    details = []
    skipped_zero = 0
    skipped_missing = 0

    for name in common_names:
        t_kernel = kernel_by_name[name].get("t_kernel")
        t_rkernel = rkernel_by_name[name].get("t_rkernel")

        # Basic validation
        if t_kernel is None or t_rkernel is None:
            skipped_missing += 1
            continue
        if t_kernel == 0:
            skipped_zero += 1
            continue

        ratio = t_rkernel / t_kernel
        ratios.append(ratio)
        if show_details:
            details.append((name, t_rkernel, t_kernel, ratio))


    if skipped_zero:
        print(f"Skipped entries with t_kernel == 0: {skipped_zero}")
    if skipped_missing:
        print(f"Skipped entries missing required fields: {skipped_missing}")



    avg_ratio = mean(ratios)
    print(f"Average t_rkernel / t_kernel: {avg_ratio:.6f}")

    if show_details:
        print("\nDetails (name, t_rkernel, t_kernel, ratio):")
        for name, trk, tk, r in details:
            print(f"{name}\t{trk}\t{tk}\t{r:.6f}")

if __name__ == "__main__":
    # Set show_details=True to print per-name details
    main(show_details=False)

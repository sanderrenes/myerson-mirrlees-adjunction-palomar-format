# MechDesigAdjointfunctor.lean → Palomar Template Adaptation

This document provides a step-by-step checklist for adapting the [MechDesigAdjointfunctor.lean](https://github.com/sanderrenes/MechDesigAdjointfunctor.lean) formalization to the Palomar template format.

**Prerequisite**: The source repository must be cloned locally for reference.

---

## Phase 1: Source Analysis (Read-Only)
- [ ] **Task 1.1**: Read `MechDesigAdjointfunctor.lean` completely
  - Identify all theorem declarations (main results)
  - Identify all definition declarations (supporting structures)
  - Identify all imports and dependencies
  - Note the namespace structure
  - Extract docstrings and mathematical context

- [ ] **Task 1.2**: Document the structure
  - Create a list of all advertised declarations (theorems to expose in Challenge.lean)
  - Create a list of all supporting definitions
  - Note any axioms or special assumptions

---

## Phase 2: Repository Setup
- [ ] **Task 2.1**: Rename package and namespace
  ```bash
  # Search and replace in all files:
  # - lakefile.toml: package name
  # - PalomarTemplate/*.lean: namespace PalomarTemplate → MechDesigAdjointfunctor
  # - Challenge.lean, Solution.lean: namespace updates
  grep -r "PalomarTemplate" . --include="*.lean" --include="*.toml" > rename_list.txt
  ```

- [ ] **Task 2.2**: Update directory structure
  ```bash
  mv PalomarTemplate MechDesigAdjointfunctor
  ```

---

## Phase 3: Content Migration

### Step 3.1: Library Content
- [ ] **Task 3.1.1**: Copy source content to library
  ```bash
  # Copy the main file to the library directory
  cp /path/to/MechDesigAdjointfunctor.lean MechDesigAdjointfunctor/
  ```

- [ ] **Task 3.1.2**: Split into logical modules if needed
  - Organize supporting definitions into separate files under `MechDesigAdjointfunctor/`
  - Ensure all imports are resolved

### Step 3.2: Challenge.lean
- [ ] **Task 3.2.1**: Create statement-only surface
  ```lean
  -- Example structure:
  import MechDesigAdjointfunctor.Definitions
  
  namespace MechDesigAdjointfunctor
  
  /-- Main theorem: Adjoint functor exists for mechanical design category -/
  theorem main_adjoint_functor_exists : ... := sorry
  
  /-- Supporting theorem: Universal property holds -/
  theorem universal_property : ... := sorry
  
  end MechDesigAdjointfunctor
  ```

- [ ] **Task 3.2.2**: Requirements
  - Every advertised declaration must have exactly one `sorry`
  - All definitions needed by statements must be included or imported
  - Docstrings must be precise and mathematical
  - Imports must resolve to Lean core, Mathlib, Tau Ceti, or CSLib only

### Step 3.3: Solution.lean
- [ ] **Task 3.3.1**: Connect declarations to proofs
  ```lean
  import MechDesigAdjointfunctor.Library
  import Challenge
  
  namespace MechDesigAdjointfunctor
  
  /-- Main theorem: Adjoint functor exists for mechanical design category -/
  theorem main_adjoint_functor_exists : ... := by
    exact Library.main_adjoint_functor_exists_proof
  
  end MechDesigAdjointfunctor
  ```

---

## Phase 4: Metadata Configuration

### Step 4.1: comparator.json
- [ ] **Task 4.1.1**: Identify all advertised declarations
  ```json
  {
    "declarations": [
      "MechDesigAdjointfunctor.main_adjoint_functor_exists",
      "MechDesigAdjointfunctor.universal_property"
    ],
    "definition_holes": []
  }
  ```

### Step 4.2: formalization.yaml
- [ ] **Task 4.2.1**: Replace ALL TEMPLATE values
  ```yaml
  project:
    name: MechDesigAdjointfunctor
    description: "Formalization of adjoint functors in mechanical design category theory"
    license: "Apache-2.0"
    
  repository:
    role: substantive-development
    
  status:
    main_results:
      - "Adjoint functor existence in mechanical design category"
      - "Universal property characterization"
    
  sources:
    - title: "Original mathematical work"
      relationship: formalizes
      type: article
      authors: ["Author Name"]
      identifier: DOI:xxxx
      location: "Journal Name, Year"
      licence: "Publisher License"
      endorsement: none
    
  proof:
    total: 5
    complete: 5
    incomplete: 0
    axioms: 0
    
  automation:
    method: manual
    tools: []
    
  fidelity:
    level: high
    
  review:
    status: none
  ```

---

## Phase 5: Dependency Management
- [ ] **Task 5.1**: Update root dependencies
  ```bash
  lake update
  ```

- [ ] **Task 5.2**: Update docbuild dependencies
  ```bash
  cd docbuild && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
  cd ..
  ```

- [ ] **Task 5.3**: Commit manifest files
  ```bash
  git add lake-manifest.json docbuild/lake-manifest.json
  git commit -m "Update dependency manifests"
  ```

---

## Phase 6: Verification

### Step 6.1: Build Verification
- [ ] **Task 6.1.1**: Build the Lean project
  ```bash
  lake exe cache get
  lake build
  ```

- [ ] **Task 6.1.2**: Build documentation
  ```bash
  cd docbuild && lake build MechDesigAdjointfunctor:docs
  cd ..
  ```

### Step 6.2: Metadata Validation
- [ ] **Task 6.2.1**: Validate formalization.yaml
  ```bash
  ruby scripts/validate-formalization.rb
  ```
  - This must report ZERO retained TEMPLATE sentinels

### Step 6.3: Comparator Verification
- [ ] **Task 6.3.1**: Run Comparator
  ```bash
  ./scripts/verify-comparator.sh
  ```
  - This verifies that Solution.lean proves Challenge.lean

---

## Phase 7: Final Checks
- [ ] **Task 7.1**: Verify no TEMPLATE values remain
  ```bash
  grep -r "TEMPLATE" . --include="*.yaml" --include="*.json" --include="*.lean"
  ```
  - Must return NO results

- [ ] **Task 7.2**: Verify LICENSE file exists
  ```bash
  test -f LICENSE && echo "LICENSE exists" || echo "MISSING LICENSE"
  ```

- [ ] **Task 7.3**: Verify project.license matches
  ```bash
  grep "license" lakefile.toml
  ```
  - Must show: `license = "Apache-2.0"`

---

## Phase 8: Submission
- [ ] **Task 8.1**: Commit all changes
  ```bash
  git add -A
  git commit -m "Adapt MechDesigAdjointfunctor.lean to Palomar template format"
  ```

- [ ] **Task 8.2**: Get commit SHA
  ```bash
  git rev-parse HEAD
  ```

- [ ] **Task 8.3**: Submit to Palomar
  - Go to: https://submit.palomar-registry.org/
  - Enter the 40-character commit SHA
  - Fill in submission details

---

## Checklist Summary

| Phase | Task | Command/Action | Verification |
|-------|------|----------------|--------------|
| 1 | Read source | `read MechDesigAdjointfunctor.lean` | List of declarations |
| 2 | Rename package | `grep -r PalomarTemplate` | No PalomarTemplate references |
| 3 | Migrate content | Copy to library | Files exist |
| 3 | Create Challenge.lean | Edit file | All declarations have sorry |
| 3 | Create Solution.lean | Edit file | All proofs complete |
| 4 | Update comparator.json | Edit file | JSON valid |
| 4 | Update formalization.yaml | Edit file | No TEMPLATE values |
| 5 | Update dependencies | `lake update` | Manifests updated |
| 6 | Build project | `lake build` | Build succeeds |
| 6 | Build docs | `lake build` in docbuild | Docs build succeeds |
| 6 | Validate metadata | `ruby scripts/validate-formalization.rb` | No sentinels |
| 6 | Run Comparator | `./scripts/verify-comparator.sh` | Passes |
| 7 | Final checks | `grep -r TEMPLATE` | No results |
| 8 | Submit | Commit + form | Submitted |

---

## Notes for LLM Agent Execution

1. **Order Matters**: Complete tasks in numerical order. Do not skip phases.

2. **Verification First**: After each major change, run the relevant verification:
   - After content changes: `lake build`
   - After metadata changes: `ruby scripts/validate-formalization.rb`
   - Before submission: `./scripts/verify-comparator.sh`

3. **Error Handling**: If any verification fails:
   - Read the error message carefully
   - Fix the specific issue
   - Re-run verification
   - Do not proceed to next phase until current phase passes

4. **File Locations**:
   - Source: `MechDesigAdjointfunctor.lean` (external, read-only reference)
   - Library: `MechDesigAdjointfunctor/` (internal, writable)
   - Challenge: `Challenge.lean` (internal, writable)
   - Solution: `Solution.lean` (internal, writable)
   - Metadata: `formalization.yaml`, `comparator.json` (internal, writable)

5. **Import Rules**:
   - Challenge.lean imports must be: Lean core, Mathlib, Tau Ceti, or CSLib
   - Solution.lean can import the library (MechDesigAdjointfunctor/)
   - Library can have arbitrary pinned Git dependencies

6. **Namespace Convention**: Use `MechDesigAdjointfunctor` as the primary namespace.

7. **Documentation**: All docstrings must be mathematically precise and complete.

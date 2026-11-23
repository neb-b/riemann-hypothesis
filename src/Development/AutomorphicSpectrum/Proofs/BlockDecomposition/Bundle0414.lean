module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

def fibM (X Z : Type) [TopologicalSpace X] [AddCommGroup Z] [Module ℂ Z] : Submodule ℂ (X → Z) where
  carrier := {φ | IsLocallyConstant φ ∧ HasCompactSupport φ}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c φ hφ := ⟨hφ.1.comp (fun z => c • z), hφ.2.comp_left (g := fun z => c • z) (smul_zero c)⟩

section Cols

variable {k : Type}

def topP (i t : ℕ) (y : Fin (i + t) → k) : Fin i → k := fun j => y (Fin.castAdd t j)

def middlePart (i t : ℕ) (y : Fin (i + t) → k) : Fin t → k := fun j => y (Fin.natAdd i j)

theorem middlePart_add [Add k] (i t : ℕ) (a b : Fin (i + t) → k) : middlePart i t (a + b) = middlePart i t a + middlePart i t b := rfl

theorem continuous_topP [TopologicalSpace k] (i t : ℕ) : Continuous (topP (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_midP [TopologicalSpace k] (i t : ℕ) : Continuous (middlePart (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

end Cols

section Act

variable {k Z : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [AddCommGroup Z] [Module ℂ Z]

def fibAct {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) :
    Representation ℂ (Multiplicative (Fin (i + t) → k)) (fibM (Fin t → k) Z) where
  toFun y :=
    { toFun := fun φ => ⟨fun v => ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)), by
        have hh : Continuous fun v : Fin t → k => v + middlePart i t y.toAdd := continuous_id.add continuous_const
        have hl : IsLocallyConstant fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) := φ.2.1.comp_continuous hh
        have hc : HasCompactSupport fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) :=
          φ.2.2.comp_homeomorph (Homeomorph.addRight (middlePart i t y.toAdd))
        exact ⟨hl.comp _, hc.comp_left (map_zero _)⟩⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext v
        exact map_add _ _ _
      map_smul' := fun c a => by
        apply Subtype.ext
        funext v
        exact map_smul _ _ _ }
  map_one' := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t 0)) (φ.1 (v + middlePart i t 0)) = φ.1 v
    have h1 : Multiplicative.ofAdd (topP (k := k) i t 0) = 1 := rfl
    have h2 : middlePart (k := k) i t 0 = 0 := rfl
    rw [h1, h2, map_one, add_zero]
    rfl
  map_mul' a b := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd))) (φ.1 (v + middlePart i t (a.toAdd + b.toAdd))) =
      ρ₀ (Multiplicative.ofAdd (topP i t a.toAdd)) (ρ₀ (Multiplicative.ofAdd (topP i t b.toAdd)) (φ.1 (v + middlePart i t a.toAdd + middlePart i t b.toAdd)))
    have h1 : Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd)) =
        Multiplicative.ofAdd (topP i t a.toAdd) * Multiplicative.ofAdd (topP i t b.toAdd) := rfl
    rw [h1, map_mul, middlePart_add, add_assoc]
    rfl

theorem fibAct_apply {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    (y : Multiplicative (Fin (i + t) → k)) (φ : fibM (Fin t → k) Z) (v : Fin t → k) :
    (fibAct t ρ₀ y φ).1 v = ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) := rfl

end Act

section Field

variable {k : Type} [Field k]

def uMh (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n where
  toFun y := uM k n y.toAdd
  map_one' := uM_zero k n
  map_mul' a b := uM_add k n a.toAdd b.toAdd

def mulH {n : ℕ} (κ : GL (Fin n) k) : Multiplicative (Fin n → k) →* Multiplicative (Fin n → k) where
  toFun y := Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec y.toAdd)
  map_one' := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec 0) = 1
    rw [Matrix.mulVec_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec (a.toAdd + b.toAdd)) = _
    rw [Matrix.mulVec_add]
    rfl

def topRep {i : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k i) V)
    (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (Multiplicative (Fin i → k)) (V ⊗[ℂ] W) where
  toFun x := LinearMap.rTensor W (τ (uM k i x.toAdd))
  map_one' := by
    show LinearMap.rTensor W (τ (uM k i 0)) = 1
    rw [uM_zero, map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    show LinearMap.rTensor W (τ (uM k i (a.toAdd + b.toAdd))) = _
    rw [uM_add, map_mul]
    exact LinearMap.rTensor_mul _ _ _

end Field

section Lat

variable {k : Type} [Field k] [ValuativeRel k]

def Lc (n : ℕ) (c : k) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {y | ∀ j, c * y.toAdd j ∈ 𝒪[k]}
  mul_mem' := by
    intro a b ha hb j
    have : c * (a * b).toAdd j = c * a.toAdd j + c * b.toAdd j := mul_add _ _ _
    rw [this]
    exact add_mem (ha j) (hb j)
  one_mem' := by
    intro j
    have : c * (1 : Multiplicative (Fin n → k)).toAdd j = 0 := mul_zero _
    rw [this]
    exact zero_mem _
  inv_mem' := by
    intro a ha j
    have : c * (a⁻¹).toAdd j = - (c * a.toAdd j) := by
      show c * (- a.toAdd j) = _
      ring
    rw [this]
    exact neg_mem (ha j)

theorem mem_Lc {n : ℕ} {c : k} {y : Multiplicative (Fin n → k)} : y ∈ Lc n c ↔ ∀ j, c * y.toAdd j ∈ 𝒪[k] := Iff.rfl

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_Lc (n : ℕ) (c : k) : IsOpen (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hset : (Lc n c : Set (Multiplicative (Fin n → k))) =
      ⋂ j, (fun y : Multiplicative (Fin n → k) => c * y.toAdd j) ⁻¹' (𝒪[k] : Set k) := by
    ext y
    simp only [SetLike.mem_coe, mem_Lc, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  have hO : IsOpen (𝒪[k] : Set k) := by exact Valuation.isOpen_integer
  exact isOpen_iInter_of_finite fun j =>
    hO.preimage (continuous_const.mul ((continuous_apply j).comp continuous_toAdd))

theorem isCompact_Lc (n : ℕ) {c : k} (hc : c ≠ 0) : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hf : Continuous fun x : Fin n → k => Multiplicative.ofAdd (c⁻¹ • x) :=
    continuous_ofAdd.comp (continuous_const_smul _)
  convert hK.image hf using 1
  ext y
  constructor
  · intro hy
    refine ⟨c • y.toAdd, fun j _ => ?_, ?_⟩
    · have h := mem_Lc.1 hy j
      rw [Valuation.mem_integer_iff] at h
      simpa using h
    · simp [smul_smul, hc]
  · rintro ⟨x, hx, rfl⟩
    refine mem_Lc.2 fun j => ?_
    rw [Valuation.mem_integer_iff]
    simpa [smul_smul, hc] using hx j trivial

end Lat

section Coset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def cosetSet (t : ℕ) (c : k) (a : Fin t → k) : Set (Fin t → k) :=
  {v | Multiplicative.ofAdd (v - a) ∈ Lc t c}

theorem isClopen_cosetSet (t : ℕ) (c : k) (a : Fin t → k) : IsClopen (cosetSet t c a) := by
  have hcont : Continuous fun v : Fin t → k => Multiplicative.ofAdd (v - a) :=
    continuous_ofAdd.comp (continuous_id.sub continuous_const)
  have h1 : IsOpen (Lc t c : Set (Multiplicative (Fin t → k))) := isOpen_Lc t c
  exact ⟨(Subgroup.isClosed_of_isOpen _ h1).preimage hcont, h1.preimage hcont⟩

theorem isCompact_cosetSet (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) : IsCompact (cosetSet t c a) := by
  have h := (isCompact_Lc t hc).image (f := fun y : Multiplicative (Fin t → k) => y.toAdd + a)
    ((continuous_toAdd).add continuous_const)
  convert h using 1
  ext v
  constructor
  · intro hv
    exact ⟨Multiplicative.ofAdd (v - a), hv, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    show Multiplicative.ofAdd (y.toAdd + a - a) ∈ Lc t c
    simpa using hy

def cosetFn (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) : fibM (Fin t → k) Z :=
  ⟨(cosetSet t c a).indicator fun _ => z, by
      classical
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ cosetSet t c a
      · exact ⟨_, (isClopen_cosetSet t c a).2, hx, fun y hy => by
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
      · exact ⟨_, (isClopen_cosetSet t c a).1.isOpen_compl, hx, fun y hy => by
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩,
    by
      haveI : T2Space k := inferInstance
      exact HasCompactSupport.intro (isCompact_cosetSet t hc a) fun x hx => Set.indicator_of_notMem hx _⟩

end Coset

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceLocalCoefficient
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth

theorem continuous_glEmb (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) :
    Continuous (glEmb k n) := by
  have hm : Continuous (glEmbMat k n) := by
    refine continuous_matrix fun a b => ?_
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b => simpa [glEmbMat] using continuous_const
    | cast a =>
      induction b using Fin.lastCases with
      | last => simpa [glEmbMat] using continuous_const
      | cast b =>
        simpa [glEmbMat] using (continuous_id.matrix_elem a b)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact hm.comp Units.continuous_val
  · exact hm.comp (Units.continuous_coe_inv)

theorem continuous_sEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : Continuous (sEmb k n) :=
  Continuous.subtype_mk ((continuous_glEmb k (n + 1)).comp continuous_subtype_val) _

theorem isOpen_rightInv {M X : Type} [Group M] [TopologicalSpace M] [IsTopologicalGroup M] (e : M → X) (A : Set M)
    (hA : IsOpen A) (h1 : (1 : M) ∈ A) (h : ∀ g ∈ A, ∀ m, e (m * g) = e m) :
    IsOpen {g : M | ∀ m, e (m * g) = e m} := by
  let T : Subgroup M :=
    { carrier := {g | ∀ m, e (m * g) = e m}
      mul_mem' := by
        intro a b ha hb m
        rw [← mul_assoc, hb, ha]
      one_mem' := by
        intro m
        rw [mul_one]
      inv_mem' := by
        intro a ha m
        have := ha (m * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  exact T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hA.mem_nhds h1) h)

section Fix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}
  {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def fixX (f : XS τ σ) : Set (Mir k ((i + 1) + (t + 1))) :=
  {x | ind (HPG k (i + 1) (t + 1)) (sigX τ σ) x (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1 =
    (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1}

theorem isOpen_fixX (f : XS τ σ) : IsOpen (fixX f) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).2

theorem one_mem_fixX (f : XS τ σ) : (1 : Mir k ((i + 1) + (t + 1))) ∈ fixX f := by
  show ind (HPG k (i + 1) (t + 1)) (sigX τ σ) 1 _ = _
  rw [map_one]
  rfl

theorem evX_mul_of_mem (f : XS τ σ) {x : Mir k ((i + 1) + (t + 1))} (hx : x ∈ fixX f)
    (p : Mir k ((i + 1) + (t + 1))) : evX f (p * x) = evX f p :=
  congrArg (fun w : indSpace (HPG k (i + 1) (t + 1)) (sigX τ σ) => w.1 p) hx

theorem intC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) :
    intC ψ f (sEmb k ((i + 1) + t) (m * g)) = intC ψ f (sEmb k ((i + 1) + t) m) := by
  unfold intC
  congr 1
  funext d
  have h2 : dEmb k i t d * sEmb k ((i + 1) + t) (m * g) =
      (dEmb k i t d * sEmb k ((i + 1) + t) m) * sEmb k ((i + 1) + t) g := by
    rw [MonoidHom.map_mul, mul_assoc]
  rw [h2]
  exact congrArg (fun v => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • v)
    (evX_mul_of_mem f h (dEmb k i t d * sEmb k ((i + 1) + t) m))

theorem eC_mul (ψ : AddChar k Circle) (f : XS τ σ) (m g : Mir k ((i + 1) + t))
    (h : sEmb k ((i + 1) + t) g ∈ fixX f) (h2 : dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1) :
    eC ψ f (m * g) = eC ψ f m := by
  have h5 : dpowM (k := k) ((i + 1) + t) (-1 / 2) (m * g) = dpowM ((i + 1) + t) (-1 / 2) m :=
    ((dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_mul m g).trans (by rw [h2, mul_one])
  unfold eC
  exact congrArg₂ (fun (c : ℂˣ) v => (c : ℂ) • qC τ σ v) h5 (intC_mul ψ f m g h)

end Fix

theorem isOpen_eC_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1))
    (σ : GRep k (t + 1)) (f : XS τ σ),
    IsOpen {g : Mir k ((i + 1) + t) | ∀ m, eC ψ f (m * g) = eC ψ f m} := by
  intro k _ _ _ _ i t ψ τ σ f
  have hA : IsOpen ((sEmb k ((i + 1) + t)) ⁻¹' fixX f) := (isOpen_fixX f).preimage (continuous_sEmb k _)
  have hB : IsOpen {g : Mir k ((i + 1) + t) | dpowM (k := k) ((i + 1) + t) (-1 / 2) g = 1} :=
    (GlobalTheory.CompanionTheory.LeibPhi.isOpen_ker_dpow k ((i + 1) + t + 1) (-1 / 2)).preimage continuous_subtype_val
  refine isOpen_rightInv (eC ψ f) _ (hA.inter hB) ⟨?_, ?_⟩ fun g hg m => eC_mul ψ f m g hg.1 hg.2
  · show sEmb k ((i + 1) + t) 1 ∈ fixX f
    rw [MonoidHom.map_one]
    exact one_mem_fixX f
  · exact (dpowM (k := k) ((i + 1) + t) (-1 / 2)).map_one

end GlobalTheory.CompanionTheory.BZPhiPG.EcSmooth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedFirstCondition
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem hecke_dominant_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hIw hpos V _ _ π hπ t t' ht ht' T T' hT hT' v l hl
  obtain ⟨r, hr, x, hxN, hx⟩ := _root_.GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps k N h d hd J hJo hJc hIw hpos t' ht'
  have hxJ : ∀ i, x i ∈ J := fun i => (hxN i).1
  have hform := _root_.GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average k N J hJc V π hπ _ T' hT' r x hr hxJ hx v
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set g := leviEmb k (stdBlocks d hd) t with hg
  set g' := leviEmb k (stdBlocks d hd) t' with hg'
  have hmul : leviEmb k (stdBlocks d hd) (t * t') = g * g' := map_mul _ _ _
  have hterm : ∀ i, l (π g (π (x i * g') (v : V))) = l (π (g * g') (v : V)) := by
    intro i
    have hc : g * x i * g⁻¹ ∈ J := (ht.1 _ (hxN i)).1
    have hfac : g * (x i * g') = (g * x i * g⁻¹) * (g * g') := by group
    have h1 : l (π (g * x i * g⁻¹) (π (g * g') (v : V))) = l (π (g * g') (v : V)) :=
      LinearMap.congr_fun (hl _ hc) _
    rw [← Module.End.mul_apply, ← map_mul, hfac, map_mul, Module.End.mul_apply, h1]
  have hTT : l (((T * T') v : fixed π J) : V) = l (π g ((T' v : fixed π J) : V)) :=
    (hT (T' v) l hl).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hTT, hform, hmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeCompatHolds
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem jacquet_hecke_operator_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ t ht T hT v
  obtain ⟨r, hr, x, hx, hu⟩ := _root_.GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps k N h d hd J hJo hJc hI hpos t ht
  have key := _root_.GlobalTheory.CompanionTheory.HeckeAvg.hecke_eq_average k N J hJc V π hπ (leviEmb k (stdBlocks d hd) t) T hT r x hr
    (fun i => (hx i).1) hu v
  have hmk : ∀ i, (Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    intro i
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨x i, (hx i).2⟩, π (leviEmb k (stdBlocks d hd) t) (v : V), ?_⟩
    simp [map_mul]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have hsum : (Submodule.Quotient.mk ((T v : fixed π J) : V) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    rw [key, Submodule.Quotient.mk_smul]
    have h2 : (Submodule.Quotient.mk (∑ i, π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
        ∑ i : Fin r, Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :=
      map_sum (Submodule.mkQ _) _ _
    rw [h2, Finset.sum_congr rfl fun i _ => hmk i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [hsum, jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Lbc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionHeckeHolds
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem jacquet_projection_hecke_intertwines : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
    PositivityTheory.SphericalProduct.A2 G := by
  intro G _ _ _ D V _ _ π hπ t ht U hU v
  obtain ⟨r, hr, x, hxJN, hx⟩ := _root_.GlobalTheory.CompanionTheory.Casselman.exists_fin_coset_reps_of_isDom G D t ht
  have hUv := _root_.GlobalTheory.CompanionTheory.HeckeAvg.heckeG_eq_average G D.J D.isOpen_J D.isCompact_J V π hπ (t : G) U hU r x hr
    (fun i => (hxJN i).1) hx v
  have hstep : ∀ i, (Submodule.Quotient.mk (π (x i * (t : G)) (v : V)) : GlobalTheory.PRep.Jacquet π D.N) =
      Submodule.Quotient.mk (π (t : G) (v : V)) := by
    intro i
    refine (Submodule.Quotient.eq _).mpr (Submodule.subset_span ⟨⟨x i, (hxJN i).2⟩, π (t : G) (v : V), ?_⟩)
    simp
  have hsum := map_sum (Submodule.mkQ (GlobalTheory.PRep.twKer π D.N 1))
    (fun i => π (x i * (t : G)) (v : V)) Finset.univ
  simp only [Submodule.mkQ_apply] at hsum
  show (Submodule.Quotient.mk (↑(U v)) : GlobalTheory.PRep.Jacquet π D.N) =
    (D.piN π t) (Submodule.Quotient.mk (v : V))
  rw [hUv, Submodule.Quotient.mk_smul, hsum]
  simp only [hstep]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hr.ne'), one_smul]
  rfl

end GlobalTheory.CompanionTheory.Cass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChange
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

theorem leviMat_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) :
    leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) =
      (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  let f : (A ⊗[F] E) →+* (A' ⊗[F] E) := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hf : ∀ e : E, f (inclR (F := F) A e) = inclR (F := F) A' e := fun e => by
    simp [f, inclR]
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (Z.map (inclR (F := F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by
    ext i j
    simp [hf]
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f :=
    fun P Q => Matrix.map_add f (map_add f) P Q
  have hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f :=
    fun P Q => Matrix.map_sub f (map_sub f) P Q
  have hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1 :=
    Matrix.map_one f (map_zero f) (map_one f)
  have hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i)) := fun d => by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  change leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f
  have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i :=
    fun _ _ => rfl
  simp only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]

end GlobalTheory.CompanionTheory.KFin
end


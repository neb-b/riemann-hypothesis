module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
public import Formalism.GelfandTransference.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTorusCommutative
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.TorComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones_eq (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [ones] at this
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [ones, hi]

theorem offDiag_of_mem {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  rw [Tor, MonoidHom.mem_range] at hx
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective j
  have hab : a ≠ b := by
    rintro rfl
    apply hij
    have hp : (p : ℕ) = 0 := by
      have := p.isLt
      simp only [ones] at this
      omega
    have hq : (q : ℕ) = 0 := by
      have := q.isLt
      simp only [ones] at this
      omega
    have hpq : p = q := Fin.ext (hp.trans hq.symm)
    rw [hpq]
  simp [leviEmb, Matrix.blockDiagonal'_apply, hab]

theorem diag_ne_zero {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  have hM : (x : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun l => (x : Matrix (Fin N) (Fin N) k) l l := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact h a b hab
  have hdet : (x : Matrix (Fin N) (Fin N) k).det ≠ 0 := (Matrix.isUnits_det_units x).ne_zero
  rw [hM, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem mem_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  rw [Tor, MonoidHom.mem_range]
  refine ⟨(fun a => Matrix.GeneralLinearGroup.scalar _
    (Units.mk0 ((x : Matrix (Fin N) (Fin N) k) a a) (diag_ne_zero x h a)) : Levi k (Bl (ones N))), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective j
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := by
      apply Fin.ext
      have hp := p.isLt
      have hq := q.isLt
      simp only [ones] at hp hq
      omega
    subst hpq
    have hs : ((stdBlocks (ones N) (sum_ones N)).symm a).fst = a := by
      have hh := stdBlocks_ones_eq N ((stdBlocks (ones N) (sum_ones N)).symm a).fst
        ((stdBlocks (ones N) (sum_ones N)).symm a).snd
      simpa using hh.symm
    simp [leviEmb, stdBlocks_ones_eq, Matrix.GeneralLinearGroup.scalar, hs]
  · rw [h _ _ (fun heq => hab (congrArg Sigma.fst ((stdBlocks (ones N) (sum_ones N)).injective heq)))]
    simp [leviEmb, Matrix.blockDiagonal'_apply, hab]

theorem eq_diagonal {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact h a b hab

theorem mul_comm_of_mem {N : ℕ} {a b : GL (Fin N) k} (ha : a ∈ Tor k N) (hb : b ∈ Tor k N) :
    a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    eq_diagonal (a : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem ha hij),
    eq_diagonal (b : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem hb hij),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem tor_comm_and_mem_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ),
    (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧
      ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔
        ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  intro k _ _ _ _ N
  exact ⟨fun a ha b hb => mul_comm_of_mem ha hb,
    fun x => ⟨fun hx i j hij => offDiag_of_mem hx hij, mem_of_offDiag x⟩⟩

end GlobalTheory.CompanionTheory.LbElem.TorComm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : (contra π).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n) (hA k n V π hs hi) hi

theorem dualCl_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr)]

theorem nonempty_equiv_contra_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (h : χ * χ' = 1) :
    Nonempty ((twist (contra π) (detChar (Fin n) χ')).Equiv (contra (twist π (detChar (Fin n) χ)))) := by
  have hψ : IsSmoothChar (detChar (Fin n) χ) := hχ.detChar
  have hinv : ∀ g : GL (Fin n) k,
      ((detChar (Fin n) χ' g : ℂˣ) : ℂ) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) := by
    intro g
    have h1 : χ (Matrix.GeneralLinearGroup.det g) * χ' (Matrix.GeneralLinearGroup.det g) = 1 := by
      rw [← MonoidHom.mul_apply, h, MonoidHom.one_apply]
    have h2 : χ' (Matrix.GeneralLinearGroup.det g) = (χ (Matrix.GeneralLinearGroup.det g))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    show ((χ' (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ)
    rw [h2, map_inv, map_inv]
  have hdual : ∀ (g : GL (Fin n) k) (l : Module.Dual ℂ V),
      (twist π (detChar (Fin n) χ)).dual g l = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π.dual g l := by
    intro g l
    apply LinearMap.ext
    intro v
    show l (((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π g⁻¹ v) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • l (π g⁻¹ v)
    exact map_smul l _ _
  have hker : ∀ g : GL (Fin n) k, g ∈ (detChar (Fin n) χ).ker →
      ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) = 1 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [map_inv, hg, inv_one, Units.val_one]
  have hkn : ((detChar (Fin n) χ).ker : Set (GL (Fin n) k)) ∈ nhds (1 : GL (Fin n) k) :=
    IsOpen.mem_nhds hψ (Subgroup.one_mem _)
  have heq : smoothPart π.dual = smoothPart (twist π (detChar (Fin n) χ)).dual := by
    ext l
    constructor
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show π.dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : π.dual g l = l := hg1
      show (twist π (detChar (Fin n) χ)).dual g l = l
      rw [hdual, hker g hg2, one_smul]
      exact h3
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show (twist π (detChar (Fin n) χ)).dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : (twist π (detChar (Fin n) χ)).dual g l = l := hg1
      rw [hdual, hker g hg2, one_smul] at h3
      show π.dual g l = l
      exact h3
  have htw : ∀ (g : GL (Fin n) k) (l : smoothPart π.dual),
      ((twist (contra π) (detChar (Fin n) χ') g l : smoothPart π.dual) : Module.Dual ℂ V) =
        ((detChar (Fin n) χ' g : ℂˣ) : ℂ) • ((contra π g l : smoothPart π.dual) : Module.Dual ℂ V) :=
    fun _ _ => rfl
  have htw2 : ∀ (g : GL (Fin n) k) (v : V),
      (twist π (detChar (Fin n) χ)) g v = ((detChar (Fin n) χ g : ℂˣ) : ℂ) • π g v :=
    fun _ _ => rfl
  exact ⟨{ toLinearEquiv := LinearEquiv.ofEq _ _ heq
           isIntertwining' := fun g => by
             apply LinearMap.ext
             intro l
             apply Subtype.ext
             apply LinearMap.ext
             intro v
             simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, htw,
               LinearMap.smul_apply, contra_apply, htw2, map_smul, smul_eq_mul, hinv] }⟩

private theorem comp_intertwiningMap_mem_smoothPart_dual {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (l : Module.Dual ℂ W) (hl : l ∈ smoothPart σ.dual) : l ∘ₗ f.toLinearMap ∈ smoothPart ρ.dual := by
  apply mem_smoothPart_of_nhds
  refine Filter.mem_of_superset (IsOpen.mem_nhds hl (by
    show σ.dual 1 l = l
    rw [map_one]
    rfl)) ?_
  intro g hg
  have h : σ.dual g l = l := hg
  show ρ.dual g (l ∘ₗ f.toLinearMap) = l ∘ₗ f.toLinearMap
  refine LinearMap.ext fun v => ?_
  calc (ρ.dual g (l ∘ₗ f.toLinearMap)) v = l (f.toLinearMap (ρ g⁻¹ v)) := rfl
    _ = l (σ g⁻¹ (f v)) := by
      rw [Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]
    _ = σ.dual g l (f v) := rfl
    _ = (l ∘ₗ f.toLinearMap) v := by
      rw [h, LinearMap.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]

private theorem nonempty_contra_equiv_of_equiv {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    Nonempty ((contra σ).Equiv (contra ρ)) := by
  refine ⟨{ toFun := fun l => ⟨l.1 ∘ₗ e.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.toIntertwiningMap l.1 l.2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            invFun := fun l => ⟨l.1 ∘ₗ e.symm.toIntertwiningMap.toLinearMap,
              comp_intertwiningMap_mem_smoothPart_dual e.symm.toIntertwiningMap l.1 l.2⟩
            left_inv := fun l => Subtype.ext (LinearMap.ext fun w => by
              show l.1 (e.toIntertwiningMap.toLinearMap (e.symm.toIntertwiningMap.toLinearMap w)) = l.1 w
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply])
            right_inv := fun l => Subtype.ext (LinearMap.ext fun v => by
              show l.1 (e.symm.toIntertwiningMap.toLinearMap (e.toIntertwiningMap.toLinearMap v)) = l.1 v
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.symm_apply_apply])
            isIntertwining' := fun g => by
              apply LinearMap.ext
              intro l
              apply Subtype.ext
              apply LinearMap.ext
              intro v
              simp only [LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, contra_apply,
                Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining] }⟩

theorem dualCl_nu : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  intro k _ _ _ _ hA x s
  have hs' : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)
  have hn' : IsSmoothChar (absPow k (-s)) := isSmoothChar_of_isUnram (isUnram_absPow k (-s))
  have hmul : absPow k s * absPow k (-s) = 1 := by
    rw [absPow_neg, mul_inv_cancel]
  have hψ : IsSmoothChar (detChar (Fin x.fst) (absPow k s)) := hs'.detChar
  have hψn : IsSmoothChar (detChar (Fin x.fst) (absPow k (-s))) := hn'.detChar
  obtain ⟨e1⟩ : Nonempty ((x.nu s).rep.Equiv (twist x.rep (detChar (Fin x.fst) (absPow k s)))) :=
    IrrRep.nonempty_equiv_rep (irrTwist x.snd.rep (detChar (Fin x.fst) (absPow k s)) hψ)
  obtain ⟨e2⟩ := nonempty_contra_equiv_of_equiv e1
  obtain ⟨e3⟩ := nonempty_equiv_contra_twist hA x.rep x.2.rep.smooth x.2.rep.irr hs' hn' hmul
  have hc := isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  obtain ⟨e4⟩ := IrrRep.nonempty_equiv_rep
    (⟨_, contra x.rep, isSmooth_contra _, hc⟩ : IrrRep (GL (Fin x.fst) k))
  have e5 := twistEquiv e4 (detChar (Fin x.fst) (absPow k (-s)))
  rw [dualCl_eq hA, dualCl_eq hA]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  exact IrrRep.cl_eq_iff.mpr ⟨(e2.symm.trans e3.symm).trans e5.symm⟩

end GlobalTheory.CompanionTheory.ZcDual

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def XA (lam : Fin n → ℤ) (B : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => fderiv ℂ (fun x : Mat n => Rm lam x i j) 1 B

def Xu (lam : Fin n → ℤ) (a b : Fin n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  XA lam (Matrix.single a b 1)

def HolRm (lam : Fin n → ℤ) : Prop :=
  ∀ (i j : Jd n lam), ∀ g ∈ GLs n, DifferentiableAt ℂ (fun x : Mat n => Rm lam x i j) g

theorem XA_add (lam : Fin n → ℤ) (B B' : Mat n) : XA lam (B + B') = XA lam B + XA lam B' := by
  ext i j; simp [XA]

theorem XA_smul (lam : Fin n → ℤ) (c : ℂ) (B : Mat n) : XA lam (c • B) = c • XA lam B := by
  ext i j; simp [XA]

theorem XA_sum (lam : Fin n → ℤ) {ι : Type} (s : Finset ι) (B : ι → Mat n) :
    XA lam (∑ r ∈ s, B r) = ∑ r ∈ s, XA lam (B r) := by
  ext i j; simp [XA, Matrix.sum_apply]

theorem Rm_of_unit (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) :
    Rm lam x = LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h)) := by
  rw [Rm, dite_eq_left h]

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Mat n) = 1 := by
  have h : IsUnit (1 : Mat n).det := by simp
  rw [Rm_of_unit lam h]
  have e : Matrix.nonsingInvUnit (1 : Mat n) h = 1 := Units.ext rfl
  rw [e, map_one]
  exact LinearMap.toMatrix_one _

theorem Rm_mul (lam : Fin n → ℤ) {x y : Mat n} (hx : IsUnit x.det) (hy : IsUnit y.det) :
    Rm lam (x * y) = Rm lam x * Rm lam y := by
  have h : IsUnit (x * y).det := by rw [Matrix.det_mul]; exact hx.mul hy
  rw [Rm_of_unit lam h, Rm_of_unit lam hx, Rm_of_unit lam hy]
  have e : Matrix.nonsingInvUnit (x * y) h = Matrix.nonsingInvUnit x hx * Matrix.nonsingInvUnit y hy := Units.ext rfl
  rw [e, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem isUnit_det_of_mem {g : Mat n} (hg : g ∈ GLs n) : IsUnit g.det := isUnit_iff_ne_zero.2 hg

theorem mem_GLs_of_isUnit {g : Mat n} (hg : IsUnit g.det) : g ∈ GLs n := hg.ne_zero

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne_fun this continuous_const

theorem hasDerivAt_line {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (i j : Jd n lam) :
    HasDerivAt (fun t : ℂ => Rm lam (1 + t • B) i j) (XA lam B i j) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => (1 : Mat n) + t • B) B 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const B).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h2 := (hD i j 1 one_mem_GLs).hasFDerivAt
  exact h2.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by simp)

theorem eventually_line_unit (B : Mat n) : ∀ᶠ t : ℂ in 𝓝 0, IsUnit ((1 : Mat n) + t • B).det := by
  have hc : Continuous fun t : ℂ => (1 : Mat n) + t • B := continuous_const.add (continuous_id.smul continuous_const)
  have : ∀ᶠ t : ℂ in 𝓝 0, (1 : Mat n) + t • B ∈ GLs n :=
    hc.continuousAt.eventually_mem (isOpen_GLs.mem_nhds (by simpa using one_mem_GLs))
  exact this.mono fun t ht => isUnit_det_of_mem ht

theorem conj_XA {lam : Fin n → ℤ} (hD : HolRm lam) {x B B' : Mat n} (hx : IsUnit x.det) (h : x * B = B' * x) :
    Rm lam x * XA lam B = XA lam B' * Rm lam x := by
  ext i j
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j = ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j := by
    filter_upwards [eventually_line_unit B, eventually_line_unit B'] with t h1 h2
    have e : x * (1 + t • B) = (1 + t • B') * x := by
      simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, h]
    have := Rm_mul lam hx h1
    rw [e, Rm_mul lam h2 hx] at this
    have := congrFun (congrFun this i) j
    simpa [Matrix.mul_apply] using this.symm
  have hL : HasDerivAt (fun t : ℂ => ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam x i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hR : HasDerivAt (fun t : ℂ => ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j)
      (∑ k, XA lam B' i k * Rm lam x k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B' i k).mul_const _
  simpa [Matrix.mul_apply] using (hL.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)).unique hR |>.symm ▸ rfl

theorem fderiv_Rm {lam : Fin n → ℤ} (hD : HolRm lam) {g : Mat n} (hg : g ∈ GLs n) (B : Mat n) (i j : Jd n lam) :
    fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B) = (Rm lam g * XA lam B) i j := by
  have hu := isUnit_det_of_mem hg
  have hline : HasDerivAt (fun t : ℂ => g + t • (g * B)) (g * B) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const (g * B)).const_add g
    rw [one_smul] at h
    exact h
  have h1 : HasDerivAt (fun t : ℂ => Rm lam (g + t • (g * B)) i j)
      (fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B)) 0 :=
    (hD i j g hg).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have h2 : HasDerivAt (fun t : ℂ => ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam g i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hev : ∀ᶠ t : ℂ in 𝓝 0, Rm lam (g + t • (g * B)) i j = ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j := by
    filter_upwards [eventually_line_unit B] with t ht
    have e : g + t • (g * B) = g * (1 + t • B) := by
      simp only [mul_add, mul_one, Matrix.mul_smul]
    rw [e, Rm_mul lam hu ht, Matrix.mul_apply]
  simpa [Matrix.mul_apply] using h1.unique (h2.congr_of_eventuallyEq hev)

end GlobalTheory.CompanionTheory.RmHol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvertibleMatrixLastLineGivenStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_matrix_last_line_given : ∀ (k : Type) [Field k] (m : ℕ) (a : Fin (m + 1) → k), a ≠ 0 → ∃ g : GL (Fin (m + 1)) k, ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = a j := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | exact GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_GL_lastRow_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_mono (n : ℕ) {s₁ s₂ : kˣ} (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    polyBall n s₁ ≤ polyBall n s₂ :=
  fun x hx i => show valuation k (x.toAdd i) ≤ valuation k (s₂ : k) from
    le_trans (show valuation k (x.toAdd i) ≤ valuation k (s₁ : k) from hx i) h

theorem exists_mem_polyBall {n : ℕ} (x : Multiplicative (Fin n → k)) :
    ∃ s : kˣ, x ∈ polyBall n s := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i : Fin n => valuation k (x.toAdd i))
  obtain ⟨y, hy⟩ := valuation_surjective (max M 1)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy.symm ▸ le_max_right M 1 : (1 : ValueGroupWithZero k) ≤ 0) (by simp)
  refine ⟨Units.mk0 y hy0, fun i => ?_⟩
  show valuation k (x.toAdd i) ≤ valuation k y
  rw [hy]
  exact le_trans (hM i) (le_max_left _ _)

theorem twKer_polyBall_mono (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨⟨x, hx⟩, v, rfl⟩
  exact Submodule.subset_span ⟨⟨x, polyBall_mono n h hx⟩, v, rfl⟩

theorem exists_mem_twKer_polyBall (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) (v : V)
    (hv : v ∈ twKer ρ ⊤ (resChr ψ a ⊤)) :
    ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, -⟩, u, rfl⟩ := hw
    obtain ⟨s, hs⟩ := exists_mem_polyBall x
    exact ⟨s, Submodule.subset_span ⟨⟨x, hs⟩, u, rfl⟩⟩
  | zero => exact ⟨1, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, h₁⟩ := hx
    obtain ⟨s₂, h₂⟩ := hy
    rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
    · exact ⟨s₂, Submodule.add_mem _ (twKer_polyBall_mono ψ ρ a h h₁) h₂⟩
    · exact ⟨s₁, Submodule.add_mem _ h₁ (twKer_polyBall_mono ψ ρ a h h₂)⟩
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, Submodule.smul_mem _ c hs⟩

end GlobalTheory.CompanionTheory.MirFourier
end


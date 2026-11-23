module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSplit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FFirstProd
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.firstProd :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL (k := k))) (h : ℕ) (y : Fin h → IrrGL (k := k)) (x : IrrGL (k := k)) (hc : ∑ i, (y i).1 = x.1), (∀ i, FirstIn (y i) P) → jhMult x.rep (prodIrr y hc) ≠ 0 → FirstIn x P := by
  intro hG hBZ k _ _ _ _ P h y x hc hy hx q hq hq0 hjm
  classical
  have h1 : jm q hq (prodIrr y hc) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hjm).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (isSmooth_parInd _ _) (jhMult_ne_zero_iff.1 hx)))
  obtain ⟨z, hr, hz, hrow, hcol⟩ := UpperTheory.Lit.Cas.cells hG hBZ k h x.1 y hc q hq h1
  have hpos : 0 < ∑ i, (z i 0).1 := (hz 0).symm ▸ hq0.1
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  obtain ⟨A, hA, w, hwA, hwP⟩ :=
    (UpperTheory.Lit.Full.piece hG hBZ k (y i) P (z i) (hr i) (hrow i)).1 (hy i) (Nat.pos_of_ne_zero hi)
  choose t ht using fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (z j 0)
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := fun j => z j 0) (hd := hz 0) ht
    (q 0).2.rep.irr (jhMult_ne_zero_iff.1 (hcol 0))
  have e1 : ∑ j, t j = {q 0} := SupportUnique.eq_singleton_of_isCusp hq0 hS
  have e2 : t i = A := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (ht i) hA
  have hw : w ∈ ∑ j, t j :=
    Multiset.mem_of_le (Finset.single_le_sum (f := t) (fun _ _ => zero_le) (Finset.mem_univ i)) (e2 ▸ hwA)
  rw [e1, Multiset.mem_singleton] at hw
  exact hw ▸ hwP
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ParIndSingle
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

open GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem parInd_single {W : Type} [AddCommGroup W] [Module ℂ W] {r : ℕ} {b : Fin r → ℕ} (a : Fin r)
    (ha : ∀ j, j ≠ a → b j = 0) (f : (Σ j, Fin (b j)) ≃ Fin (b a))
    (ρ : Representation ℂ (Levi k fun j => Fin (b j)) W) :
    IsSubquotient (parInd f ρ) (ρ.comp (MonoidHom.mulSingle (fun j => GL (Fin (b j)) k) a) :
      Representation ℂ (GL (Fin (b a)) k) W) := by
  let f' := GlobalTheory.OneBlockCell.valEquiv (n := b) a rfl ha
  have hf' : ∀ i, f' ⟨a, i⟩ = i := fun i => rfl
  obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ f f' W).1 ρ
  refine (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans ?_
  have h1 : ∀ g : GL (Fin (b a)) k, leviEmb k f' (Pi.mulSingle a g) = g := fun g => by
    ext i j
    conv_lhs => rw [← hf' i, ← hf' j]
    rw [leviEmb_apply_same]
    simp
  have law : ∀ (F : IndSp f' ρ) (g : GL (Fin (b a)) k), F.1.1 g = ρ (Pi.mulSingle a g) (F.1.1 1) := by
    intro F g
    have h4 := parInd_law f' _ F ⟨_, leviEmb_mem_parab k f' (Pi.mulSingle a g)⟩ 1
    rw [leviProj_leviEmb, GlobalTheory.OneBlockCell.deltaHalf_eq_one_of_single a ha, Units.val_one, one_smul] at h4
    simpa only [h1, mul_one] using h4
  let ι : (parInd f' ρ).IntertwiningMap (ρ.comp (MonoidHom.mulSingle (fun j => GL (Fin (b j)) k) a) :
      Representation ℂ (GL (Fin (b a)) k) W) :=
    { toFun := fun F => F.1.1 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun g => LinearMap.ext fun F => by
        show F.1.1 (1 * g) = ρ (Pi.mulSingle a g) (F.1.1 1)
        rw [one_mul, law] }
  refine .of_injective ι fun F G h => Subtype.ext (Subtype.ext (funext fun g => ?_))
  have h' : F.1.1 1 = G.1.1 1 := h
  rw [law F, law G, h']

private theorem eq_of_jm {r : ℕ} (q : Fin r → IrrGL (k := k)) (a : Fin r) (ha : ∀ j, j ≠ a → (q j).1 = 0) (x : IrrGL (k := k))
    (hq : ∑ j, (q j).1 = x.1) (h : jm q hq x.rep ≠ 0) : q a = x := by
  obtain ⟨d, y⟩ := x
  obtain rfl : (q a).1 = d := by
    rwa [Finset.sum_eq_single a (fun j _ hj => ha j hj) (by simp)] at hq
  have h1 := jhMult_ne_zero_iff.1 h
  obtain ⟨ψ⟩ := nonempty_equiv_of_isSubquotient (q a).2.rep.irr y.rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (q j).rep) (fun j => (q j).2.rep.irr) a).trans
      ((isSubquotient_comp h1 _).trans (isSubquotient_jac_single (b := fun j => (q j).1) a ha _ _)))
  exact (IrrGL.of_rep (q a)).symm.trans ((IrrGL.of_eq_of.2 ⟨ψ.symm⟩).trans (IrrGL.of_rep ⟨_, y⟩))

private theorem eq_of_jh {r : ℕ} (q : Fin r → IrrGL (k := k)) (a : Fin r) (ha : ∀ j, j ≠ a → (q j).1 = 0) (x : IrrGL (k := k))
    (hq : ∑ j, (q j).1 = x.1) (h : jhMult x.rep (prodIrr q hq) ≠ 0) : q a = x := by
  obtain ⟨d, y⟩ := x
  obtain rfl : (q a).1 = d := by
    rwa [Finset.sum_eq_single a (fun j _ hj => ha j hj) (by simp)] at hq
  have h1 := jhMult_ne_zero_iff.1 h
  obtain ⟨ψ⟩ := nonempty_equiv_of_isSubquotient y.rep.irr (q a).2.rep.irr
    (isSubquotient_factor (fun j => (q j).rep) a y.rep.irr
      (h1.trans (parInd_single (b := fun j => (q j).1) a ha _ _)))
  exact (IrrGL.of_rep (q a)).symm.trans ((IrrGL.of_eq_of.2 ⟨ψ⟩).trans (IrrGL.of_rep ⟨_, y⟩))

private theorem cell (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {P : Set (IrrGL (k := k))} {x y z y' z' : IrrGL (k := k)} (h : Emb x y z) (h' : Emb x y' z') (hy' : SuppIn y' P)
    (hz : FirstIn z Pᶜ) :
    ∃ (s : Fin 2 → Fin 2 → IrrGL (k := k)) (hr : ∀ i, ∑ j, (s i j).1 = (![y, z] i).1)
      (hc : ∀ j, ∑ i, (s i j).1 = (![y', z'] j).1), (∀ i, jm (s i) (hr i) (![y, z] i).rep ≠ 0) ∧
        (∀ j, jhMult (![y', z'] j).rep (prodIrr (fun i => s i j) (hc j)) ≠ 0) ∧ (s 1 0).1 = 0 := by
  obtain ⟨hd, f, hf⟩ := h
  obtain ⟨hd', f', hf'⟩ := h'
  have hτ : (piTensor fun j => (![y', z'] j).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k _ _ fun j => (![y', z'] j).2.rep
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (![y', z'] a).1) hd') hτ f'
    ⟨v, fun e => hv (hf' (e.trans (map_zero f').symm))⟩
  have h2 : jm ![y', z'] hd' (prodIrr ![y, z] hd) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h1)).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (isSmooth_prodIrr _ _) (.of_injective f hf)))
  obtain ⟨s, hr, hc, hrow, hcol⟩ := UpperTheory.Lit.Cas.cells hG hBZ k 2 x.1 ![y, z] hd ![y', z'] hd' h2
  refine ⟨s, hr, hc, hrow, hcol, ?_⟩
  by_contra hne
  obtain ⟨A, hA, w, hwA, hwP⟩ := (UpperTheory.Lit.Full.piece hG hBZ k z Pᶜ (s 1) (hr 1) (hrow 1)).1 hz
    (Nat.pos_of_ne_zero hne)
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (s 0 0)
  obtain ⟨C, hC, hCP⟩ := hy'
  have h3 : HasSupport y'.rep (∑ i, ![B, A] i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := fun i => s i 0) (hd := hc 0)
      (fun i => by fin_cases i; exacts [hB, hA]) y'.2.rep.irr (jhMult_ne_zero_iff.1 (hcol 0))
  have h4 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hC h3
  refine hwP (hCP w ?_)
  rw [h4, Fin.sum_univ_two]
  exact Multiset.mem_add.2 (Or.inr hwA)

end

theorem UpperTheory.Lit.Full.data :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL (k := k))) (x y z y' z' : IrrGL (k := k)), Emb x y z → Emb x y' z' → SuppIn y P → SuppIn y' P → FirstIn z Pᶜ → FirstIn z' Pᶜ → y = y' ∧ z = z' := by
  intro hG hBZ k _ _ _ _ P x y z y' z' h h' hy hy' hz hz'
  obtain ⟨s, hr, hc, hrow, hcol, h10⟩ := cell hG hBZ h h' hy' hz
  obtain ⟨t, hr', hc', -, -, h10'⟩ := cell hG hBZ h' h hy hz'
  have r0 : (s 0 0).1 + (s 0 1).1 = y.1 := (Fin.sum_univ_two fun j => (s 0 j).1).symm.trans (hr 0)
  have c0 : (s 0 0).1 + (s 1 0).1 = y'.1 := (Fin.sum_univ_two fun i => (s i 0).1).symm.trans (hc 0)
  have r0' : (t 0 0).1 + (t 0 1).1 = y'.1 := (Fin.sum_univ_two fun j => (t 0 j).1).symm.trans (hr' 0)
  have c0' : (t 0 0).1 + (t 1 0).1 = y.1 := (Fin.sum_univ_two fun i => (t i 0).1).symm.trans (hc' 0)
  have h01 : (s 0 1).1 = 0 := by omega
  have hoff : ∀ i j, j ≠ i → (s i j).1 = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    exacts [absurd rfl hij, h01, h10, absurd rfl hij]
  have key : ∀ i, ![y, z] i = ![y', z'] i := fun i =>
    (eq_of_jm (s i) i (hoff i) _ (hr i) (hrow i)).symm.trans
      (eq_of_jh (fun j => s j i) i (fun j hj => hoff j i hj.symm) _ (hc i) (hcol i))
  exact ⟨key 0, key 1⟩
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TProdExp
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem jac_equiv_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    Nonempty ((jac e π).Equiv (jac e τ)) := by
  refine ⟨Representation.Equiv.mk' (jacMap e φ.toIntertwiningMap)
    (jacMap e φ.symm.toIntertwiningMap) ?_ ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ.symm (φ v)) = Submodule.Quotient.mk v
      simp
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ (φ.symm v)) = Submodule.Quotient.mk v
      simp

private theorem cell_exp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hC : CasselmanNecSq k) (δ : IrrGL (k := k))
    (h1 : 1 ≤ δ.1) (h2 : IsSqIntCoeff δ.rep) (y : Fin 2 → IrrGL (k := k)) (hr : ∑ j, (y j).1 = δ.1)
    (hj : jm y hr δ.rep ≠ 0) (t : kˣ) (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0))
    (a : Fin 2 → ℂ) (ha : ∀ j, ScalarBy (y j) t (a j)) : ‖a 0‖ ≤ 1 ∧ ‖a 0‖ * ‖a 1‖ = 1 := by
  obtain ⟨⟨c, hc⟩, -, -⟩ := schur hA k δ t
  have hu : ‖c‖ = 1 := unitcent k δ.1 _ δ.rep 2 δ.snd.rep.smooth δ.snd.rep.irr h2 t c hc
  have hprod : a 0 * a 1 = c := split k δ.1 _ δ.rep y hr hj t c (a 0) (a 1) hc (ha 0) (ha 1)
  have hnorm : ‖a 0‖ * ‖a 1‖ = 1 := by rw [← norm_mul, hprod, hu]
  refine ⟨?_, hnorm⟩
  by_cases h0 : (y 0).1 = 0
  · rw [(schur hA k (y 0) t).2.2 (a 0) h0 (ha 0), norm_one]
  by_cases h1' : (y 1).1 = 0
  · rw [(schur hA k (y 1) t).2.2 (a 1) h1' (ha 1), norm_one, mul_one] at hnorm
    exact hnorm.le
  have hpos : ∀ j : Fin 2, 0 < (y j).1 :=
    Fin.forall_fin_two.2 ⟨Nat.pos_of_ne_zero h0, Nat.pos_of_ne_zero h1'⟩
  have hE := hC δ.1 δ.rep h1 δ.snd.rep.smooth δ.snd.rep.irr h2 2 y hr hpos hj
  have hlt := (hE t ht a ha).1 0 (by norm_num)
  have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
  rw [hf, Finset.prod_singleton] at hlt
  exact hlt.le

theorem UpperTheory.Lit.Cas.prodExp :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CasselmanNecSq k → ∀ (h N : ℕ) (δ : Fin h → IrrGL (k := k)) (hd : ∑ i, (δ i).1 = N), (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible → Nonempty (π.Equiv (prodIrr δ hd)) → UnitaryCentral π ∧ MaxExpWeak π := by
  intro hG hBZ hA k _ _ _ _ hC h N δ hd hδ V _ _ π hirr hφ
  obtain ⟨φ⟩ := hφ
  haveI := nontrivial_of_irreducible hirr
  constructor
  · intro t c hc
    choose b hb using fun i => (schur hA k (δ i) t).1
    have hbn : ∀ i, ‖b i‖ = 1 := fun i =>
      unitcent k (δ i).1 _ (δ i).rep 2 (δ i).snd.rep.smooth (δ i).snd.rep.irr (hδ i).2 t (b i) (hb i)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hφv : φ.toLinearEquiv v ≠ 0 := by
      rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
    have e1 : φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v)
        = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) :=
      LinearMap.congr_fun
        (φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.scalar (Fin N) t)) v
    have e2 : c • φ.toLinearEquiv v = (∏ i, b i) • φ.toLinearEquiv v :=
      calc c • φ.toLinearEquiv v = φ.toLinearEquiv (c • v) :=
            (LinearEquiv.map_smul φ.toLinearEquiv c v).symm
        _ = φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v) :=
            congrArg _ (hc v).symm
        _ = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) := e1
        _ = (∏ i, b i) • φ.toLinearEquiv v := scalarFull k h N δ hd t b hb _
    have hcb : c = ∏ i, b i := smul_left_injective ℂ hφv e2
    rw [hcb, norm_prod]
    exact Finset.prod_eq_one (fun i _ => hbn i)
  · intro x hx hpos hj
    have hjm : jm x hx (prodIrr δ hd) ≠ 0 := by
      obtain ⟨ψ⟩ := jac_equiv_of_equiv (stdBlocks (fun a => (x a).1) hx) φ
      unfold jm at hj ⊢
      rwa [← jhMult_congr_right _ ψ]
    obtain ⟨y, hr, hcc, hyj, hxj⟩ := cells hG hBZ k h N δ hd x hx hjm
    intro t ht c hcx
    choose a ha using fun i j => (schur hA k (y i j) t).1
    have hcj : ∀ j, c j = ∏ i, a i j := fun j =>
      (schur hA k (x j) t).2.1 _ _ (hcx j)
        (scalarProd k h (fun i => y i j) (x j) (hcc j) t (fun i => a i j) (fun i => ha i j) (hxj j))
    have hcell : ∀ i, ‖a i 0‖ ≤ 1 ∧ ‖a i 0‖ * ‖a i 1‖ = 1 := fun i =>
      cell_exp hA hC (δ i) (hδ i).1 (hδ i).2 (y i) (hr i) (hyj i) t ht (a i) (ha i)
    have n0 : ‖c 0‖ ≤ 1 := by
      rw [hcj 0, norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => (hcell i).1)
    have n01 : ‖c 0‖ * ‖c 1‖ = 1 := by
      rw [hcj 0, hcj 1, norm_prod, norm_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => (hcell i).2)
    refine ⟨fun j hj' => ?_, by rw [Fin.prod_univ_two]; exact n01⟩
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
    rw [hf, Finset.prod_singleton]
    exact n0
end


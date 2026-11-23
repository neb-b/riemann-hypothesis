module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GEmb
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

theorem gEmb (e1 : TensorProductVectors) (e2 : LeviSubgroupRestriction) (e3 : ParabolicInductionKernel) (e4 : InducedDeterminantTwist)
    (e5 : InductionExtension) : GEmb := by
  intro k _ _ _ _ n G V _ _ π hπ
  obtain ⟨X, instA, instM, σ, -, -, hdet, ⟨e⟩⟩ := hπ
  let _ := instA
  let _ := instM
  obtain ⟨v, hv0, hv⟩ := e1 k G.s G.d X σ G.μ hdet
  choose F hF using fun φ : ↥G.V0sp => e5 e2 e3 k n G X σ v hv φ.1 φ.2
  have hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ := fun φ ψ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (φ + ψ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      have h3 := hF ψ ⟨κ, hκ⟩
      change _ = (F φ).1.1 κ + (F ψ).1.1 κ
      rw [h1, h2, h3, ← add_smul]
      rfl
  have hsmul : ∀ (c : ℂ) φ, F (c • φ) = c • F φ := fun c φ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (c • φ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      change _ = c • (F φ).1.1 κ
      rw [h1, h2, smul_smul]
      rfl
  let f0 : ↥G.V0sp →ₗ[ℂ] IndSp G.e (piTensor σ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ f0, fun φ ψ h => ?_, fun κ φ φ' hφ' => ?_⟩
  · have h' : F φ = F ψ := e.symm.toLinearEquiv.injective h
    refine Subtype.ext (funext fun κ => ?_)
    have h2 := congrArg (fun F : IndSp G.e (piTensor σ) => F.1.1 (κ : GL (Fin n) k)) h'
    simp only [hF] at h2
    exact smul_left_injective ℂ hv0 h2
  · have key : F φ' = parInd G.e (piTensor σ) (κ : GL (Fin n) k) (F φ) :=
      e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun x hx => by
        rw [hF φ' ⟨x, hx⟩, parInd_apply, hF φ ⟨x * κ, mul_mem hx κ.2⟩, hφ']
        rfl
    change e.symm.toLinearEquiv (F φ') = π κ (e.symm.toLinearEquiv (F φ))
    rw [key, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap (κ : GL (Fin n) k) (F φ)

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_indDetK

theorem eq_of_eqOn_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (F F' : IndSp (stdBlocks d hd) ρ)
    (h : ∀ κ ∈ KO k (Fin n), F.1.1 κ = F'.1.1 κ) : F = F' := by
  have hfun : F.1.1 = F'.1.1 := by
    funext x
    obtain ⟨p, w, hw, rfl⟩ :=
      GlobalTheory.SmGL.MultiIrr.exists_parab_mul (GlobalTheory.SmGL.stdBlocks d hd) x
    rw [GlobalTheory.SmGL.parInd_law, GlobalTheory.SmGL.parInd_law,
      h w hw]
  exact Subtype.ext (Subtype.ext hfun)

end P_indDetK

theorem step_indDetK : InducedDeterminantTwist := by
  intro k _ _ _ _ s n d hd W _ _ ρ F F' h
  exact P_indDetK.eq_of_eqOn_KO d hd ρ F F' h

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndExt
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct Pointwise

namespace UpperTheory.TNZ

namespace P_indExt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hne : ((ϖ : k) ^ r) ≠ 0 := pow_ne_zero _ fun h => hϖ.ne_zero (Subtype.ext h)
  have e : {x : k | InPow r x} = ((ϖ : k) ^ r) • (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_ofPred_eq, InPow, Set.mem_smul_set, smul_eq_mul]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨(z : k), z.2, by simp only [map_mul, map_pow]; rw [mul_comm]; rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ϖ ^ r * ⟨z, hz⟩, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), by simp only [map_mul, map_pow]; rfl⟩
  have hO : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  rw [e]
  exact hO.smul₀ hne

theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ i, ⋂ j,
      (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact (isOpen_inPow r).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem one_mem_KC (n r : ℕ) : (1 : GL (Fin n) k) ∈ KC k n r := by
  refine ⟨one_mem _, fun i j => ⟨0, zero_mem _, ?_⟩⟩
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

section Ext

variable {n : ℕ} (G : Grp k n) {X : Fin G.s → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  (σ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (X a))

def extFun (φ : ↥(KO k (Fin n)) → ℂ) (v : ⨂[ℂ] a, X a) (x : GL (Fin n) k) : ⨂[ℂ] a, X a :=
  (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e (MultiIrr.exists_parab_mul G.e x).choose) : ℂ) •
    piTensor σ (leviProj k G.e (MultiIrr.exists_parab_mul G.e x).choose)
      (φ ⟨(MultiIrr.exists_parab_mul G.e x).choose_spec.choose,
        (MultiIrr.exists_parab_mul G.e x).choose_spec.choose_spec.1⟩ • v)

variable {G σ}

theorem expr_eq (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v)
    (p p' : parab k G.e) (w w' : GL (Fin n) k) (hw : w ∈ KO k (Fin n)) (hw' : w' ∈ KO k (Fin n))
    (he : (p : GL (Fin n) k) * w = p' * w') :
    (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p') : ℂ) • piTensor σ (leviProj k G.e p') (φ ⟨w', hw'⟩ • v) =
      (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p) : ℂ) • piTensor σ (leviProj k G.e p) (φ ⟨w, hw⟩ • v) := by
  obtain ⟨hφ1, -⟩ := hφ
  obtain ⟨q, rfl⟩ : ∃ q : parab k G.e, p = p' * q := ⟨p'⁻¹ * p, (mul_inv_cancel_left p' p).symm⟩
  have hw'eq : w' = (q : GL (Fin n) k) * w := by
    rw [Subgroup.coe_mul, mul_assoc] at he
    exact (mul_left_cancel he).symm
  have hqK : (q : GL (Fin n) k) ∈ KO k (Fin n) := by
    have : (q : GL (Fin n) k) = w' * w⁻¹ := by rw [hw'eq, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hw' (inv_mem hw)
  subst hw'eq
  have h1 : φ ⟨(q : GL (Fin n) k) * w, hw'⟩ = G.lam (q : GL (Fin n) k) * φ ⟨w, hw⟩ :=
    hφ1 ⟨q, hqK⟩ ⟨hqK, q.2⟩ ⟨w, hw⟩
  have hP' := hP k G.s n G.d G.hd q hqK
  have hδ : deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e q) = 1 := hP'.2
  have hρ : piTensor σ (leviProj k G.e q) v = G.lam (q : GL (Fin n) k) • v := by
    rw [hv _ hP'.1, hL k n G q hqK]
  rw [(leviProj k G.e).map_mul p' q, (deltaHalf k (fun a => Fin (G.d a))).map_mul, hδ, mul_one,
    (piTensor σ).map_mul, Module.End.mul_apply, map_smul (piTensor σ (leviProj k G.e q)), hρ, h1, smul_smul, mul_comm]

theorem extFun_mul (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v)
    (p : parab k G.e) (w : GL (Fin n) k) (hw : w ∈ KO k (Fin n)) :
    extFun G σ φ v ((p : GL (Fin n) k) * w) =
      (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p) : ℂ) • piTensor σ (leviProj k G.e p) (φ ⟨w, hw⟩ • v) := by
  obtain ⟨hw', he⟩ := (MultiIrr.exists_parab_mul G.e ((p : GL (Fin n) k) * w)).choose_spec.choose_spec
  exact expr_eq hL hP hφ hv p _ w _ hw hw' he

theorem extFun_mem (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) :
    extFun G σ φ v ∈ indSpace (parab k G.e)
      ((twist (piTensor σ) (deltaHalf k (fun a => Fin (G.d a)))).comp (leviProj k G.e)) := by
  intro h g
  obtain ⟨p, w, hw, rfl⟩ := MultiIrr.exists_parab_mul G.e g
  rw [← mul_assoc, ← Subgroup.coe_mul, extFun_mul hL hP hφ hv (h * p) w hw, extFun_mul hL hP hφ hv p w hw]
  generalize φ ⟨w, hw⟩ • v = x
  rw [MonoidHom.comp_apply, twist_apply, map_smul, smul_smul, (leviProj k G.e).map_mul,
    (deltaHalf k (fun a => Fin (G.d a))).map_mul, Units.val_mul, (piTensor σ).map_mul, Module.End.mul_apply]

theorem exists_ext (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) :
    ∃ F : IndSp G.e (piTensor σ), ∀ κ : ↥(KO k (Fin n)), F.1.1 κ = φ κ • v := by
  have hφ' := hφ
  obtain ⟨-, hφ2⟩ := hφ'
  refine ⟨⟨⟨extFun G σ φ v, extFun_mem hL hP hφ hv⟩, ?_⟩, fun κ => ?_⟩
  · refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((isOpen_KC n G.lev).mem_nhds (one_mem_KC n G.lev))
      fun u hu => ?_)
    refine Subtype.ext (funext fun x => ?_)
    show extFun G σ φ v (x * u) = extFun G σ φ v x
    obtain ⟨p, w, hw, rfl⟩ := MultiIrr.exists_parab_mul G.e x
    have h2 : φ ⟨w * u, mul_mem hw hu.1⟩ = φ ⟨w, hw⟩ := hφ2 ⟨w, hw⟩ ⟨u, hu.1⟩ hu
    rw [mul_assoc, extFun_mul hL hP hφ hv p (w * u) (mul_mem hw hu.1), h2, extFun_mul hL hP hφ hv p w hw]
  · have h := extFun_mul hL hP hφ hv 1 κ κ.2
    rw [Subgroup.coe_one, one_mul] at h
    show extFun G σ φ v κ = _
    rw [h, map_one, map_one, map_one, Units.val_one, one_smul, Module.End.one_apply]

end Ext

end P_indExt

theorem step_indExt : InductionExtension := by
  intro hL hP k _ _ _ _ n G X _ _ σ v hv φ hφ
  exact P_indExt.exists_ext hL hP hφ hv

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamLevi
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_lamLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tele {H : Type} [CommGroup H] (ν : ℕ → H) (b : ℕ) :
    ∀ s, b ≤ s → ∏ i ∈ Finset.range s, (if b ≤ i then ν i / ν (i + 1) else 1) = ν b / ν s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base =>
    rw [div_self', Finset.prod_eq_one]
    intro i hi
    rw [if_neg (by simpa using hi)]
  | succ s hbs ih =>
    rw [Finset.prod_range_succ, ih, if_pos hbs, div_mul_div_cancel]

variable {n : ℕ} (G : Grp k n)

theorem prod_ge (b : Fin G.s) :
    ∏ a : Fin G.s, (if b ≤ a then G.μ a / G.μnext a else 1) = G.μ b := by
  let ν : ℕ → (kˣ →* ℂˣ) := fun i => if h : i < G.s then G.μ ⟨i, h⟩ else 1
  have h1 : ∀ a : Fin G.s, (if b ≤ a then G.μ a / G.μnext a else 1) =
      (fun i : ℕ => if (b : ℕ) ≤ i then ν i / ν (i + 1) else 1) a := by
    intro a
    have ha : ν a = G.μ a := by simp [ν, a.isLt]
    have hn : ν (a + 1) = G.μnext a := rfl
    simp only [ha, hn, Fin.le_iff_val_le_val]
  rw [Finset.prod_congr rfl (fun a _ => h1 a),
    Fin.prod_univ_eq_prod_range (fun i : ℕ => if (b : ℕ) ≤ i then ν i / ν (i + 1) else 1) G.s,
    tele ν b G.s b.isLt.le]
  have hb : ν b = G.μ b := by simp [ν, b.isLt]
  have hs : ν G.s = 1 := by simp [ν]
  rw [hb, hs, div_one]

theorem Δ_parab (p : parab k G.e) (a : Fin G.s) :
    G.Δ a (p : GL (Fin n) k) =
      ((∏ b : Fin G.s, (if b ≤ a then GeneralLinearGroup.det (leviProj k G.e p b) else 1) : kˣ) : k) := by
  unfold Grp.Δ
  set M' : Matrix {i : Fin n // G.bl i ≤ a} {i : Fin n // G.bl i ≤ a} k :=
    ((p : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).submatrix Subtype.val Subtype.val with hM'
  have hbt : M'.BlockTriangular (fun i => G.bl i.val) := fun i j h => p.2 h
  rw [BlockTriangular.det_fintype hbt, Units.coe_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs with hb
  · rw [GeneralLinearGroup.val_det_apply]
    let f : Fin (G.d b) ≃ {j : {i : Fin n // G.bl i ≤ a} // G.bl j.val = b} :=
      Equiv.ofBijective (fun i => ⟨⟨G.e ⟨b, i⟩, by simp [Grp.bl, hb]⟩, by simp [Grp.bl]⟩) ⟨fun i j h => by
        simpa using h, by
          rintro ⟨⟨i, hi⟩, hib⟩
          obtain ⟨⟨c, j⟩, rfl⟩ := G.e.surjective i
          obtain rfl : c = b := by simpa [Grp.bl] using hib
          exact ⟨j, rfl⟩⟩
    rw [← det_submatrix_equiv_self f]
    rfl
  · have : IsEmpty {j : {i : Fin n // G.bl i ≤ a} // G.bl j.val = b} :=
      ⟨fun j => hb (j.2 ▸ j.1.2)⟩
    rw [det_isEmpty, Units.val_one]

end P_lamLevi

open P_lamLevi in
theorem step_lamLevi : LeviSubgroupRestriction := by
  intro k _ _ _ _ n G p _
  set D : Fin G.s → kˣ := fun b => GeneralLinearGroup.det (leviProj k G.e p b) with hD
  have hΔ : ∀ a, G.Δ a (p : GL (Fin n) k) = ((∏ b, (if b ≤ a then D b else 1) : kˣ) : k) :=
    fun a => Δ_parab G p a
  have hchk : ∀ a, Grp.chk (G.μ a / G.μnext a) (G.Δ a (p : GL (Fin n) k)) =
      (((G.μ a / G.μnext a) (∏ b, (if b ≤ a then D b else 1)) : ℂˣ) : ℂ) := by
    intro a
    rw [Grp.chk, dite_eq_right (by rw [hΔ a]; exact Units.ne_zero _)]
    congr 3
    ext
    simp [hΔ a]
  unfold Grp.lam
  rw [Finset.prod_congr rfl (fun a _ => hchk a), ← Units.coe_prod, ← Units.coe_prod]
  congr 1
  simp_rw [map_prod, apply_ite (G.μ _ / G.μnext _), map_one]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← prod_ge G b, MonoidHom.finsetProd_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  split_ifs <;> simp [hD]

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ParabolicMaximalCompact
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace ParabolicMaximalCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviProj_mem_KO {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd))
    (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (a : Fin s) :
    leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a)) := by
  rw [GlobalTheory.StepData.mem_KO] at hp ⊢
  have hinv : ((GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p a)⁻¹ :
      GL (Fin (d a)) k) =
      GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p⁻¹ a := by
    rw [map_inv, Pi.inv_apply]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GlobalTheory.SmGL.leviProj_apply]
    exact hp.1 _ _
  · rw [hinv, GlobalTheory.SmGL.leviProj_apply]
    exact hp.2 _ _

end ParabolicMaximalCompact

theorem step_parabKO : ParabolicInductionKernel := by
  intro k _ _ _ _ s n d hd p hp
  have h := fun a => ParabolicMaximalCompact.leviProj_mem_KO d hd p hp a
  exact ⟨h, deltaHalf_of_mem_leviK ((Subgroup.mem_pi _).2 fun a _ => h a)⟩

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

namespace TensorVector

theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (x : ∀ a, X a) (hx : ∀ a, x a ≠ 0) :
    PiTensorProduct.tprod ℂ x ≠ 0 := by
  choose ℓ hℓ using fun a => Module.Projective.exists_dual_eq_one ℂ (hx a)
  intro h
  have h1 := congrArg (PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)) h
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at h1
  simp [hℓ] at h1

end TensorVector

theorem step_tensorVec : TensorProductVectors := by
  intro k _ _ _ _ s d X _ _ σ μ h
  choose x hx0 hx using h
  refine ⟨PiTensorProduct.tprod ℂ x, TensorVector.tprod_ne_zero x hx0, fun m hm => ?_⟩
  rw [piTensor_tprod]
  have : (fun a => σ a (m a) (x a)) =
      fun a => ((μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ) • x a :=
    funext fun a => hx a (m a) (hm a)
  rw [this, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]

end UpperTheory.TNZ
end
end


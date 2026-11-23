module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EvLemOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.evLem_of :
    UpperTheory.Gal.Wt.EvLem := by
  intro M X Z _ _ _ ev hsep T Φ hT L
  let W : Submodule ℂ (Module.Dual ℂ M) := Submodule.span ℂ (Set.range ev)
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_dualCoannihilator] at hm
    exact (Submodule.mem_bot ℂ).2 (hsep m fun x => hm _ (Submodule.subset_span ⟨x, rfl⟩))
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot, Submodule.dualAnnihilator_bot]
  let φ : Module.Dual ℂ M →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun l z => l (Φ z)
      map_add' := fun a b => by
        ext z
        simp
      map_smul' := fun c a => by
        ext z
        simp }
  have hle : W ≤ T.comap φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hT x
  have hL : L ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hle hL
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExistsDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_one (a k : ℕ) : tor a k 1 = 1 := by
  apply Units.ext
  rw [tor_coe]
  simp

private theorem top_ne {a : ℕ} (κ : DomWeight a) : top κ ≠ 0 := by
  intro h
  have h1 : extremal ℂ a κ = 0 := congrArg Subtype.val h
  exact Formalism.GradedWeylDivisibility.hwNe ℂ a a le_rfl _ h1

private theorem exists_dual {a : ℕ} {κ : DomWeight a} {w : nablaSq ℂ a κ} (hw : w ≠ 0) :
    ∃ L : nablaSq ℂ a κ →ₗ[ℂ] ℂ, L w ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 hc)

private theorem span_top {a : ℕ} {κ : DomWeight a} (A : Set (nablaSq ℂ a κ)) (hA : ∃ w ∈ A, w ≠ 0)
    (hst : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∀ w ∈ A, sqRep ℂ a κ (unitaryIncl a u) w ∈ A) :
    Submodule.span ℂ A = ⊤ := by
  let S : Subrepresentation (smallRep (unitaryIncl a) κ) :=
    ⟨Submodule.span ℂ A, fun u x hx => by
      change sqRep ℂ a κ (unitaryIncl a u) x ∈ Submodule.span ℂ A
      induction hx using Submodule.span_induction with
      | mem x h => exact Submodule.subset_span (hst u x h)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx⟩
  rcases (isIrreducible_smallRep_unitary a κ).eq_bot_or_eq_top S with h | h
  · exfalso
    obtain ⟨w, hw, hw0⟩ := hA
    have h1 : Submodule.span ℂ A = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hw0 ((Submodule.span_eq_bot.1 h1) w hw)
  · exact congrArg Subrepresentation.toSubmodule h

theorem UpperTheory.Gal.Wt.wtBd_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.ExpDisj → UpperTheory.Gal.Wt.SqExp → UpperTheory.Gal.Wt.TopUp → UpperTheory.Gal.Wt.TorFacts → UpperTheory.Gal.Wt.WtBd := by
  intro hB hD hS hT hF a k κ s
  have hz1 : ∀ f : Circle → ℂ, f = 0 → f 1 = 0 := fun f h => by rw [h]; rfl
  refine ⟨fun A hA hst hexp => ?_, fun w hw hexp => ?_⟩
  · have htop : Submodule.span ℂ A = ⊤ := span_top A hA hst
    by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual (top_ne κ)
    have hall : ∀ x ∈ Submodule.span ℂ A, (fun z => L (sqRep ℂ a κ (tor a k z) x)) ∈ ExpLe s := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x h => exact hexp x h L
      | zero =>
        have h0 := (ExpLe s).zero_mem
        convert h0 using 1
        funext z
        simp only [map_zero, Pi.zero_apply]
      | add x y _ _ hx hy =>
        have := (ExpLe s).add_mem hx hy
        convert this using 1
        funext z
        simp only [map_add, Pi.add_apply]
      | smul c x _ hx =>
        have := (ExpLe s).smul_mem c hx
        convert this using 1
        funext z
        simp only [map_smul, Pi.smul_apply]
    have hmem := hall (top κ) (htop.ge Submodule.mem_top)
    have hfun : (fun z => L (sqRep ℂ a κ (tor a k z) (top κ))) = fun z : Circle => L (top κ) * (z : ℂ) ^ psum κ k := by
      funext z
      obtain ⟨hup, -, hchi, -⟩ := hF a k z
      rw [hT a κ _ hup, hchi κ, map_smul, smul_eq_mul, mul_comm]
    rw [hfun] at hmem
    have hge := (hB.2.2.2.1 (L (top κ)) (psum κ k)).2
    have h0 := hz1 _ (hD s (psum κ k) _ hlt hmem hge)
    simp at h0
    exact hL h0
  · by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := exists_dual hw
    have h0 := hz1 _ (hD (psum κ k) s _ hlt (hS a k κ w L).1 (hexp L))
    simp only [tor_one, map_one, Module.End.one_apply] at h0
    exact hL h0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpBasic
section
noncomputable section

namespace UpperTheory.Gal.Wt

private theorem pow_mem_le {s m : ℤ} (h : m ≤ s) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpLe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem pow_mem_ge {s m : ℤ} (h : s ≤ m) : (fun z : Circle => (z : ℂ) ^ m) ∈ ExpGe s :=
  Submodule.subset_span ⟨m, h, rfl⟩

private theorem circle_mul_mem_of_mem_span_of_mem_span {S T : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, ∀ g ∈ T, (fun z => f z * g z) ∈ P) {f g : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) (hg : g ∈ Submodule.span ℂ T) :
    (fun z => f z * g z) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS =>
    induction hg using Submodule.span_induction with
    | mem g hgT => exact h f hfS g hgT
    | zero =>
      have e : (fun z => f z * (0 : Circle → ℂ) z) = 0 := by
        funext z
        simp
      rw [e]
      exact P.zero_mem
    | add g₁ g₂ _ _ h₁ h₂ =>
      have e : (fun z => f z * (g₁ + g₂) z) = (fun z => f z * g₁ z) + (fun z => f z * g₂ z) := by
        funext z
        simp [mul_add]
      rw [e]
      exact P.add_mem h₁ h₂
    | smul c g _ h₁ =>
      have e : (fun z => f z * (c • g) z) = c • (fun z => f z * g z) := by
        funext z
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact P.smul_mem c h₁
  | zero =>
    have e : (fun z => (0 : Circle → ℂ) z * g z) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z => (f₁ + f₂) z * g z) = (fun z => f₁ z * g z) + (fun z => f₂ z * g z) := by
      funext z
      simp [add_mul]
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z => (c • f) z * g z) = c • (fun z => f z * g z) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_comp_inv_mem_of_mem_span {S : Set (Circle → ℂ)} {P : Submodule ℂ (Circle → ℂ)}
    (h : ∀ f ∈ S, (fun z : Circle => f z⁻¹) ∈ P) {f : Circle → ℂ}
    (hf : f ∈ Submodule.span ℂ S) : (fun z : Circle => f z⁻¹) ∈ P := by
  induction hf using Submodule.span_induction with
  | mem f hfS => exact h f hfS
  | zero =>
    have e : (fun z : Circle => (0 : Circle → ℂ) z⁻¹) = 0 := by
      funext z
      simp
    rw [e]
    exact P.zero_mem
  | add f₁ f₂ _ _ h₁ h₂ =>
    have e : (fun z : Circle => (f₁ + f₂) z⁻¹) = (fun z => f₁ z⁻¹) + (fun z => f₂ z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.add_mem h₁ h₂
  | smul c f _ h₁ =>
    have e : (fun z : Circle => (c • f) z⁻¹) = c • (fun z => f z⁻¹) := by
      funext z
      simp
    rw [e]
    exact P.smul_mem c h₁

private theorem circle_zpow_mul_zpow_eq_zpow_add (m n : ℤ) :
    (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) = fun z : Circle => (z : ℂ) ^ (m + n) := by
  funext z
  rw [zpow_add₀ (Circle.coe_ne_zero z)]

private theorem circle_inv_zpow_eq_zpow_neg (m : ℤ) :
    (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) = fun z : Circle => (z : ℂ) ^ (-m) := by
  funext z
  rw [Circle.coe_inv, inv_zpow, zpow_neg]

theorem expBasic_of : ExpBasic := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_le (by omega)
  · intro s t f g hf hg
    refine circle_mul_mem_of_mem_span_of_mem_span ?_ hf hg
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    show (fun z : Circle => (z : ℂ) ^ m * (z : ℂ) ^ n) ∈ _
    rw [circle_zpow_mul_zpow_eq_zpow_add]
    exact pow_mem_ge (by omega)
  · intro s t hst
    constructor
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hm.trans hst, rfl⟩
    · show Submodule.span ℂ _ ≤ Submodule.span ℂ _
      apply Submodule.span_mono
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨m, hst.trans hm, rfl⟩
  · intro c m
    exact ⟨(ExpLe m).smul_mem c (pow_mem_le le_rfl), (ExpGe m).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro c
    have e : (fun _ : Circle => c) = c • (fun z : Circle => (z : ℂ) ^ (0 : ℤ)) := by
      funext z
      simp
    rw [e]
    exact ⟨(ExpLe 0).smul_mem c (pow_mem_le le_rfl), (ExpGe 0).smul_mem c (pow_mem_ge le_rfl)⟩
  · intro s f
    constructor
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_ge (by omega)
    · intro hf
      refine circle_comp_inv_mem_of_mem_span ?_ hf
      rintro _ ⟨m, hm, rfl⟩
      show (fun z : Circle => ((z⁻¹ : Circle) : ℂ) ^ m) ∈ _
      rw [circle_inv_zpow_eq_zpow_neg]
      exact pow_mem_le (by omega)

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpDisj
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private noncomputable def chiZ (m : ℤ) : Circle →* ℂ where
  toFun z := (z : ℂ) ^ m
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow]

private theorem chiZ_injective : Function.Injective chiZ := by
  intro m n h
  by_contra hmn
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  set z : Circle := Circle.exp (Real.pi / (m - n : ℤ)) with hz
  have hpow : (z : ℂ) ^ (m - n) = -1 := by
    rw [hz, Circle.coe_exp, ← Complex.exp_int_mul]
    have : ((m - n : ℤ) : ℂ) * (((Real.pi / ((m - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have hk' : ((m - n : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
      push_cast
      push_cast at hk'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h1 : (z : ℂ) ^ m = (z : ℂ) ^ n := DFunLike.congr_fun h z
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have h2 : (z : ℂ) ^ (m - n) = 1 := by
    rw [zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]
  rw [h2] at hpow
  norm_num at hpow

theorem UpperTheory.Gal.Wt.expDisj_of :
    UpperTheory.Gal.Wt.ExpDisj := by
  intro s t f hst hle hge
  let v : ℤ → (Circle → ℂ) := fun m z => (z : ℂ) ^ m
  have hli : LinearIndependent ℂ v :=
    (linearIndependent_monoidHom Circle ℂ).comp chiZ chiZ_injective
  have hd : Disjoint (Set.Iic s) (Set.Ici t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hx) hst) (not_lt.mpr (Set.mem_Ici.mp hx'))
  have hdisj := hli.disjoint_span_image hd
  have e1 : ExpLe s = Submodule.span ℂ (v '' Set.Iic s) := by
    unfold ExpLe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  have e2 : ExpGe t = Submodule.span ℂ (v '' Set.Ici t) := by
    unfold ExpGe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  rw [e1] at hle
  rw [e2] at hge
  exact Submodule.disjoint_def.mp hdisj f hle hge
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamExOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem cEmb_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) {c : UA E n}
    (hc : c ∈ finU (E := E) (n := n)) : cEmb τ c = 1 := by
  have : cInf c = 1 := hc
  simp [cEmb, this]

theorem UpperTheory.Gal.Wt.famEx_of : NeatLev → EllC → Twist → TwistBd → Kap0 → Pieces → DeltaNear → FamOf → FamEx := by
  intro hN hE hT hTB hK hP hD hF E _ _ _ l _ ι a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf τ hτ X b hb ε hε
  classical
  obtain ⟨C, hC, hKC, hneat, hint, hfC⟩ := hN E l Fact.out a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf
  obtain ⟨ℓ, hℓ⟩ := hE E a C hC.fin hneat
  obtain ⟨R, hR0, hR⟩ := hTB E l ι a C hC ℓ hℓ W f X b hb
  obtain ⟨κ, hκr, hκi, hκ1, hκc, hκI⟩ := hK E l ι a v' τ hτ
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  let φ : C →* GL (Fin a) ℂ := κ.comp C.subtype
  have hφI : ∀ c : C, IntGL ι (φ c) := fun c => hκI _ (hint _ c.2)
  obtain ⟨Q, _, c, P, hQ⟩ := hP l ι a C φ (fun i j => (hκc i j).comp continuous_subtype_val) hφI
    ((Kv.comap (cLoc v')).subgroupOf C)
    (hKo.preimage ((GlobalTheory.BCT.GlobLev.continuous_cLoc v').comp continuous_subtype_val))
    (fun x hx => by
      have h1 : cLoc v' x.1 = 1 := (hκ1 _).1 hx
      change cLoc v' x.1 ∈ Kv
      rw [h1]; exact Kv.one_mem) (ε / R) (div_pos hε hR0)
  choose F hFC hFv using fun q => hT E a C hC ℓ hℓ W f (c q)
  let M : UA E a → GL (Fin a) ℂ := fun g => (cEmb τ g)⁻¹ * κ g
  let n : UA E a → GL (Fin a) ℂ := fun g => φ (ℓ g) * (M g)⁻¹
  have hn : IsNrm τ C n := by
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun x hx g => ?_⟩
    · simp only [n, M, hℓ.left γ hγ, map_mul, hκr γ hγ]
      group
    · have := hℓ.lev ⟨k, hk⟩ g
      have e : φ ⟨k, hk⟩ = κ k := rfl
      simp only [n, M] at this ⊢
      rw [this]
      simp only [map_mul, cEmb_fin τ (hC.fin hk), e]
      group
    · simp only [n, M, hℓ.inf x hx, map_mul, hκi x hx]
      group
  obtain ⟨d, hd⟩ := hF E a τ C hC n hn W Q F hFC P
  refine ⟨d, M, fun g h hh h1 => ?_, fun ν => ?_⟩
  · simp only [M, map_mul, cEmb_fin τ hh, (hκ1 h).2 h1, mul_one]
  have hfam := hd ν fun q => (φ (c q))⁻¹
  refine ⟨_, ⟨hfam.aut, fun k hk => hfam.fix k (hKC hk), hfam.inf, hfam.up, hfam.le, hfam.ge, hfam.fin⟩, fun g i => ?_⟩
  obtain ⟨q₀, h0, h1, h2, h3⟩ := hQ (ℓ g)
  have hnM : n g * M g = φ (ℓ g) := by simp only [n]; group
  have hε' : 0 ≤ ε / R := (div_pos hε hR0).le
  have hv : f.1 (b g i) g = (F q₀).1 (b g i) g := by
    rw [hFv, ← hfC ((c q₀)⁻¹ * ℓ g : C) ⟨Subtype.prop _, h0⟩ (b g i) (g * ((ℓ g)⁻¹ * c q₀ : C))]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hδ : ∀ q, (φ (c q))⁻¹ * φ (ℓ g) = φ ((c q)⁻¹ * ℓ g) := fun q => by rw [map_mul, map_inv]
  rw [famOf_apply, hv, hnM]
  have e : (F q₀).1 (b g i) g - ∑ q, pev (P q) (φ (ℓ g)) * delta ν ((φ (c q))⁻¹ * φ (ℓ g)) * (F q).1 (b g i) g =
      ∑ q, ((if q = q₀ then 1 else 0) - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g))) * (F q).1 (b g i) g := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hδ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le fun q _ => ?_
  rw [map_mul, norm_mul, hFv, ← div_mul_cancel₀ ε hR0.ne']
  refine mul_le_mul ?_ (hR _ _ _) (norm_nonneg _) hε'
  obtain ⟨hb1, hb2⟩ := hD l ι a ν _ (hφI ((c q)⁻¹ * ℓ g))
  by_cases hq : q = q₀
  · subst hq
    have hb3 := hb2 _ hε' h1
    rw [if_pos rfl]
    have e2 : 1 - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g)) =
        -((pev (P q) (φ (ℓ g)) - 1) * delta ν (φ ((c q)⁻¹ * ℓ g)) + (delta ν (φ ((c q)⁻¹ * ℓ g)) - 1)) := by ring
    rw [e2, map_neg, norm_neg, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hb3)
    rw [map_mul, norm_mul]
    exact (mul_le_mul h2 hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
  · rw [if_neg hq, zero_sub, map_neg, norm_neg, map_mul, norm_mul]
    exact (mul_le_mul (h3 q hq) hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfA
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.famOfA_of :
    UpperTheory.Gal.Wt.AutMul → UpperTheory.Gal.Wt.NrmAut → UpperTheory.Gal.Wt.RFinEx → UpperTheory.Gal.Wt.FamOfA := by
  intro hMul hNrm hR E _ _ _ a τ C hC n hn W ν Q _ f P X
  have hp := fun q => hNrm E a τ C hC n hn (pev (P q)) ((hR a).2 (P q))
  have hd := fun q => hNrm E a τ C hC n hn (fun m => delta ν (X q * m)) ((hR a).1 ν (X q))
  have key : ∀ y₁ y₂ v, famOf n ν f P X y₁ y₂ v =
      ∑ q, ((fun g => pev (P q) (n g * y₂)) * (fun g => delta ν (X q * (n g * y₁)))) * (f q).1 v := by
    intro y₁ y₂ v
    funext g
    rw [famOf_apply, Finset.sum_apply]
    rfl
  refine ⟨fun y₁ y₂ v => ?_, ?_⟩
  · rw [key]
    exact mem_autU.1 (Submodule.sum_mem _ fun q _ => mem_autU.2
      (hMul E a _ _ (hMul E a _ _ ((hp q).1 y₂) ((hd q).1 y₁)) ((f q).2.1 v)))
  · choose S₁ hS₁f hS₁ using fun q => (hp q).2
    choose S₂ hS₂f hS₂ using fun q => (hd q).2
    have hfin : ∀ q, FiniteDimensional ℂ ↥(S₁ q * S₂ q * LinearMap.range (f q).1) := fun q => by
      have h₁ : (S₁ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₁f q)
      have h₂ : (S₂ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₂f q)
      have h₃ : (LinearMap.range (f q).1).FG := Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
      exact Submodule.fg_iff_finiteDimensional _ |>.1 ((h₁.mul h₂).mul h₃)
    refine ⟨⨆ q, S₁ q * S₂ q * LinearMap.range (f q).1, Submodule.finiteDimensional_iSup _, ?_⟩
    intro y₁ y₂ v
    rw [key]
    exact Submodule.sum_mem _ fun q _ => Submodule.mem_iSup_of_mem q
      (Submodule.mul_mem_mul (Submodule.mul_mem_mul (hS₁ q y₂) (hS₂ q y₁)) (LinearMap.mem_range_self _ v))
end


module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionFramesMoveToCoverAndRingExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreTorsionEqReductions
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupport
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaBasisAfterEveryFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis.AllExt

open GlobalTheory.FramePull GlobalTheory.ConstFam

variable {S Z : Scheme.{0}} {G₀ : Over S} {G : Over Z} {L₀ : LB G₀.left} {L : LB G.left} {F : G.left ⟶ G₀.left}
  {π : Z ⟶ S} {N : ℕ} {w : LB.Iso L (L₀.pull F)}

theorem exists_cmp_inv (hF : IsPullback F G.hom G₀.hom π) {T : Over Z} {T₀ : Over S} {u : T.left ⟶ T₀.left}
    {v : T₀.left ⟶ T.left} (huv : u ≫ v = 𝟙 _) (hvu : v ≫ u = 𝟙 _) (hu : u ≫ T₀.hom = T.hom ≫ π)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left ∧
        Ψ ≫ Φ = 𝟙 _ ∧ Φ ≫ Ψ = 𝟙 _ := by
  have w₀ : (snd T₀ G₀).left ≫ G₀.hom = (((fst T₀ G₀).left ≫ v) ≫ T.hom) ≫ π := by
    rw [Category.assoc, Category.assoc, ← hu, reassoc_of% hvu, Over.w, Over.w]
  obtain ⟨Ψ, c₁, c₂⟩ : ∃ Ψ : (T₀ ⊗ G₀).left ⟶ (T ⊗ G).left,
      Ψ ≫ (fst T G).left = (fst T₀ G₀).left ≫ v ∧ Ψ ≫ (snd T G).left = hF.lift _ _ w₀ :=
    ⟨pullback.lift ((fst T₀ G₀).left ≫ v) (hF.lift _ _ w₀) (hF.lift_snd _ _ w₀).symm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have c₃ : Ψ ≫ (snd T G).left ≫ F = (snd T₀ G₀).left := by
    rw [reassoc_of% c₂, hF.lift_fst]
  refine ⟨Ψ, c₁, c₃, FramePull.prod_ext ?_ ?_, FramePull.prod_ext ?_ ?_⟩
  · rw [Category.assoc, a₁, reassoc_of% c₁, hvu, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, a₂, c₃, Category.id_comp]
  · rw [Category.assoc, c₁, reassoc_of% a₁, huv, Category.id_comp, Category.comp_id]
  · rw [Category.id_comp]
    apply hF.hom_ext
    · rw [Category.assoc, Category.assoc, c₃, a₂]
    · rw [Category.assoc, Category.assoc, reassoc_of% c₂, hF.lift_snd, reassoc_of% a₁,
        reassoc_of% huv, Over.w, Over.w]

theorem basis_up (hF : IsPullback F G.hom G₀.hom π) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL : L.IsLB) {V : Scheme.{0}}
    {χ : V ⟶ Z} {χ₀ : V ⟶ S} (hχ : χ₀ = χ ≫ π) {T : Over Z} {T₀ : Over S} {h : Over.mk χ ⟶ T} {h₀ : Over.mk χ₀ ⟶ T₀}
    {u : T.left ⟶ T₀.left} (e : h₀.left = h.left ≫ u)
    {Φ : (T ⊗ G).left ⟶ (T₀ ⊗ G₀).left} (a₁ : Φ ≫ (fst T₀ G₀).left = (fst T G).left ≫ u)
    (a₂ : Φ ≫ (snd T₀ G₀).left = (snd T G).left ≫ F) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {b₀ : Fin n → LB.Sec (LPow G₀ L₀ (N : ℤ) T₀)}
    (hb : ∀ i, TransportedAlt w Φ (b i) (b₀ i)) (H : BasisAlong G L N h b) : BasisAlong G₀ L₀ N h₀ b₀ := by
  have hu : 𝟙 V ≫ (Over.mk χ₀).hom = (Over.mk χ).hom ≫ π := (Category.id_comp _).trans hχ
  obtain ⟨Φ', b₁, b₂⟩ := exists_cmp hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (𝟙 V) hu
  obtain ⟨Ψ, c₁, c₃, i₁, i₂⟩ := exists_cmp_inv hF (T := Over.mk χ) (T₀ := Over.mk χ₀) (u := 𝟙 V) (v := 𝟙 V)
    (Category.id_comp _) (Category.id_comp _) hu b₁ b₂
  have hc := cmp_comm (h := h) (h₀ := h₀) a₁ a₂ b₁ b₂ ((Category.id_comp _).trans e)
  replace b₁ : Φ' ≫ (fst (Over.mk χ₀) G₀).left = (fst (Over.mk χ) G).left := b₁.trans (Category.comp_id _)
  replace c₁ : Ψ ≫ (fst (Over.mk χ) G).left = (fst (Over.mk χ₀) G₀).left := c₁.trans (Category.comp_id _)
  intro s₀
  obtain ⟨s, hs⟩ := exists_thr_down hw hL₀ hL b₂ s₀
  refine (existsUnique_congr fun c => ?_).2 (H s)
  rw [FramePull.lin_iff, FramePull.lin_iff]
  constructor
  · intro H W r z J hJ
    obtain ⟨J₀, hJ₀⟩ := exists_good' hL₀ z
    have := H W (r ≫ Φ') z J₀ hJ₀
    rw [Category.assoc r Φ' (fst (Over.mk χ₀) G₀).left, b₁] at this
    exact (lin_at_iff hc hb hs r z hJ₀ hJ _).1 this
  · intro H W r z J₀ hJ₀
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have := (lin_at_iff hc hb hs (r ≫ Ψ) z hJ₀ hJ _).2 (H W (r ≫ Ψ) z J hJ)
    rw [Category.assoc r Ψ Φ', i₁, Category.comp_id, Category.assoc r Ψ, c₁] at this
    exact this

theorem exists_allBasis : Laws → Laws2 → ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (A : PolAV (Sp K)) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), AllBasis G₀ L₀ k x τ := by
  intro hL _ Z G₀ _ L₀ hL₀ K _ x A φ w gp hw k hk
  obtain ⟨U, hU, b, hb⟩ := PolFrames.exists_local_basisAlong k hL.secBaseChange A hk (IsLocalRing.closedPoint K)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have huv : (⊤ : (Sp K).Opens).ι ≫ (Sp K).topIso.inv = 𝟙 _ := (Sp K).topIso.hom_inv_id
  have hvu : (Sp K).topIso.inv ≫ (⊤ : (Sp K).Opens).ι = 𝟙 _ := (Sp K).topIso.inv_hom_id
  obtain ⟨Φ, a₁, a₂⟩ := exists_cmp gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    (⊤ : (Sp K).Opens).ι rfl
  obtain ⟨Ψ, -, c₃, -, i₂⟩ := exists_cmp_inv gp.1 (T := Over.mk (⊤ : (Sp K).Opens).ι) (T₀ := Over.mk x)
    huv hvu rfl a₁ a₂
  choose τ hτ using fun i => exists_thr_up hw hL₀ A.isLB c₃ i₂ (b i)
  refine ⟨_, τ, fun K' _ ga x' h => ?_⟩
  have e : spMap ga = (spMap ga ≫ (Sp K).topIso.inv) ≫ (⊤ : (Sp K).Opens).ι := by
    rw [Category.assoc, hvu, Category.comp_id]
  exact basis_up gp.1 hw hL₀ A.isLB (h.symm.trans (congrArg (· ≫ x) e)) e a₁ a₂ hτ
    (hb K' (spMap ga ≫ (Sp K).topIso.inv))

end GlobalTheory.OneBasis.AllExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionMapOfThetaMatching
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.TorsMatch

theorem txT_zero {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) :
    N.txT m p 0 = N.uth m p.1.2.b 1 := by
  simp only [NumD.txT, NumD.vt, NumD.wQ, NumB.uth, NumB.mth, NumB.uV, hp, toAdd_one, NumD.ψ_zero, NumD.Gt.s_zero,
    NumD.c_zero, N.cub.N_one, N.cub.face, _root_.one_mul, div_one, NumD.Gt.pow_b, Units.val_one, div_eq_mul_inv,
    Units.val_mul, inv_one]
  ring

variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (mt : Match N N' n)

theorem exists_partner (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) (p : N.QT K) (hp : p.1.1 = 1) :
    ∃ p', mt.r K p p' ∧ p'.1.1 = 1 := by
  subst hK
  obtain ⟨p', h⟩ := mt.tot i p
  obtain ⟨z, hz⟩ := (hA.2 i p p' h).1.1 ⟨0, by rw [hp, smul_zero, toAdd_one]⟩
  refine ⟨p' * N'.qTriv _ (-z), (mt.eqv _ p p p' _ h ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ i • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

theorem partner_b (hn : n ≠ 0) (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) {p q : N.QT K} {p' q' : N'.QT K}
    (h : mt.r K p p') (h' : mt.r K q q') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) (hq : q.1.1 = 1) (hq' : q'.1.1 = 1)
    (hb : p.1.2.b = q.1.2.b) : p'.1.2.b = q'.1.2.b := by
  subst hK
  obtain ⟨t, ht⟩ := mt.tot i (p⁻¹ * q)
  have hT : N.InT (p⁻¹ * q) := ⟨_, (N.qEq_equivalence _).refl _, by
      change p.1.1⁻¹ * q.1.1 = 1
      rw [hp, hq, inv_mul_cancel], by
      change p.1.2.b⁻¹ * q.1.2.b = 1
      rw [hb, inv_mul_cancel]⟩
  obtain ⟨t', e, t1, t2⟩ := (hA.2 i _ _ ht).2.1 hT
  have r1 := mt.mul _ _ _ _ _ h ((mt.eqv _ _ _ _ _ ht ((N.qEq_equivalence _).refl _)).2 e)
  rw [mul_inv_cancel_left] at r1
  obtain ⟨z, z1, z2⟩ := (mt.eqv _ _ _ _ _ r1 ((N.qEq_equivalence _).refl _)).1 h'
  change _ = p'.1.1.toAdd + t'.1.1.toAdd + _ at z1
  rw [hq', hp', t1, toAdd_one, add_zero, zero_add, ← natCast_zsmul] at z1
  have hz : z = 0 := (smul_eq_zero_iff_right (Int.natCast_ne_zero.2 (pow_ne_zero i hn))).1 z1.symm
  rw [hz, N'.io_zero, _root_.mul_one] at z2
  rw [z2]
  change _ = p'.1.2.b * t'.1.2.b
  rw [t2, _root_.mul_one]

theorem raise {k k' K : ℕ} (hk : k' ≠ 0) (hK : K = k * k') {p : N.QT k} {p' : N'.QT k} (h : mt.r k p p')
    (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) :
    ∃ q q', mt.r K q q' ∧ q.1.1 = 1 ∧ q'.1.1 = 1 ∧ q.1.2 = p.1.2 ∧ q'.1.2 = p'.1.2 := by
  subst hK
  refine ⟨⟨(1, p.1.2), ?_⟩, ⟨(1, p'.1.2), ?_⟩, ?_, rfl, rfl, rfl, rfl⟩
  · rw [NumD.mem_QT, pow_mul, N.mem_QT.1 p.2, hp, toAdd_one, N.io_zero, one_pow]
  · rw [NumD.mem_QT, pow_mul, N'.mem_QT.1 p'.2, hp', toAdd_one, N'.io_zero, one_pow]
  · exact (mt.incl k k' p p' _ _ hk (((congrArg (· ^ k') hp).trans (one_pow k')).symm) rfl
      (((congrArg (· ^ k') hp').trans (one_pow k')).symm) rfl).1 h

theorem exists_pair [IsAlgClosed C] (hn : n ≠ 0) (hA : mt.A) (i K : ℕ) (hK : K = n ^ i) (b : N.A) (hb : b ^ K = 1) :
    ∃ p p', mt.r K p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  obtain ⟨u, h, h'⟩ := QStr.root_over N (hK ▸ pow_ne_zero i hn : K ≠ 0) 1 b hb
  obtain ⟨p', r, hp'⟩ := exists_partner mt hA i K hK ⟨(1, u), h'.trans N.io_zero.symm⟩ rfl
  exact ⟨_, p', r, rfl, hp', h⟩

theorem exists_map (hn : n ≠ 0) (hA : mt.A) (i : ℕ) : ∃ ρ : N.A → N'.A, ∀ K, K = n ^ i →
    ∀ p p', mt.r K p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b := by
  classical
  refine ⟨fun b => if h : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = b
    then h.choose.2.1.2.b else 1, ?_⟩
  rintro K rfl p p' h hp hp'
  have ex : ∃ x : N.QT (n ^ i) × N'.QT (n ^ i), mt.r _ x.1 x.2 ∧ x.1.1.1 = 1 ∧ x.2.1.1 = 1 ∧ x.1.1.2.b = p.1.2.b :=
    ⟨(p, p'), h, hp, hp', rfl⟩
  obtain ⟨a, b, c, d⟩ := ex.choose_spec
  beta_reduce
  rw [dite_eq_left ex]
  exact partner_b mt hn hA i _ rfl h a hp hp' b c d.symm

theorem exists_torsMap : AllMatch fun {_} _ {N} {N'} {n} mt _ _ => mt.A → ∀ e, mt.Term e → ∀ j : ℕ, ∃ ρ : N.A → N'.A, TorsMap N.toNumB N'.toNumB (n ^ j) mt.c₀ ρ ∧ (∀ i, i ≤ 2 * j → ∀ p p', mt.r (n ^ i) p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = ρ p.1.2.b) ∧ ∀ b : N.A, b ^ (n ^ j) ^ 2 = 1 → ∃ p p', mt.r (n ^ (2 * j)) p p' ∧ p.1.1 = 1 ∧ p'.1.1 = 1 ∧ p.1.2.b = b := by
  intro C _ _ _ _ N N' q q' n g g' hp _ _ _ _ _ _ mt hA e hT j
  have hn : n ≠ 0 := hp.ne_zero
  have hK : (n ^ j) ^ 2 = n ^ (2 * j) := by rw [← pow_mul, mul_comm]
  obtain ⟨ρ, hρ⟩ := exists_map mt hn hA (2 * j)
  refine ⟨ρ, ⟨fun b b' hb hb' => ?_, fun b hb => ?_⟩, fun i hi p p' h h1 h1' => ?_, fun b hb => ?_⟩
  · obtain ⟨p, p', h, h1, h2, rfl⟩ := exists_pair mt hn hA _ _ hK b hb
    obtain ⟨r, r', h', h3, h4, rfl⟩ := exists_pair mt hn hA _ _ hK b' hb'
    rw [← hρ _ hK p p' h h1 h2, ← hρ _ hK r r' h' h3 h4]
    refine ⟨(hρ _ hK _ _ (mt.mul _ _ _ _ _ h h') ?_ ?_).symm, ?_⟩
    · change p.1.1 * r.1.1 = 1
      rw [h1, h3, _root_.mul_one]
    · change p'.1.1 * r'.1.1 = 1
      rw [h2, h4, _root_.mul_one]
    · rw [← N.wp_of_eq_zero p r h1 h3, ← N'.wp_of_eq_zero p' r' h2 h4]
      exact mt.wp _ _ _ _ _ h h'
  · obtain ⟨p, p', h, h1, h2, rfl⟩ := exists_pair mt hn hA _ _ hK b hb
    rw [← hρ _ hK p p' h h1 h2]
    refine ⟨by rw [N'.QT_pow_b, h2, toAdd_one, N'.c_zero], ?_⟩
    have t := hT j p p' h h1 h2 0
    rwa [map_zero, txT_zero _ _ _ h1, txT_zero _ _ _ h2] at t
  · obtain ⟨r, r', h', h3, h4, h5, h6⟩ := raise mt (K := n ^ (2 * j)) (pow_ne_zero (2 * j - i) hn)
      (by rw [← pow_add, Nat.add_sub_cancel' hi]) h h1 h1'
    rw [← h5, ← h6]
    exact hρ _ rfl r r' h' h3 h4
  · exact exists_pair mt hn hA _ _ rfl b (hK ▸ hb)

end GlobalTheory.Ex.TorsMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionValue

theorem exists_torsion_pullback {B B' : Scheme.{0}} (H : Over B) [GrpObj H] (r : B' ⟶ B) (c : Over.mk r ⟶ H) (n : ℕ)
    (hc : c ^ n = 1) : ∃ c' : baseOver B' ⟶ (Over.pullback r).obj H, c' ^ n = 1 ∧
      c'.left ≫ pullback.fst H.hom r = c.left := by
  have h := isGrpPullback_pullback H r
  let c' : baseOver B' ⟶ (Over.pullback r).obj H :=
    Over.homMk (pullback.lift c.left (𝟙 B') ((Over.w c).trans (Category.id_comp r).symm)) (pullback.lift_snd _ _ _)
  have e : c'.left ≫ pullback.fst H.hom r = c.left := pullback.lift_fst _ _ _
  let U : Over.mk ((baseOver B').hom ≫ r) ⟶ Over.mk r := Over.homMk (𝟙 B') rfl
  have e₁ : pushHom h _ c' = preHom U c := Over.OverMorphism.ext (e.trans (Category.id_comp _).symm)
  have e₂ : pushHom h _ (c' ^ n) = pushHom h _ 1 := by
    rw [map_pow, e₁, ← map_pow, hc, map_one, map_one]
  refine ⟨c', ?_, e⟩
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e₂
  · rw [Over.w, Over.w]

theorem cl_of_test {C : GlobalTheory.ZJ.Core} {p : ℕ} [Fact p.Prime] {y : Sp (GlobalTheory.ZJ.OO p) ⟶ C.Z} (τ : C.Test y) : C.Cl y := by
  let k : τ.V →+* PadicAlgCl p := (GlobalTheory.ZJ.OO p).subtype.comp τ.j
  have hk : Function.Injective k := Subtype.val_injective.comp τ.j_inj
  have e : GlobalTheory.ZJ.gPt p ≫ spMap τ.j = spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ jK τ.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (IsFractionRing.lift_algebraMap (K := FractionRing τ.V) hk x).symm
  have e2 : GlobalTheory.ZJ.gPt p ≫ y = (spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold GlobalTheory.ZJ.Core.Cl
  rw [e2]
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact ((spMap (IsFractionRing.lift (K := FractionRing τ.V) hk) ≫ τ.yK) w).2

theorem isDominant_gPt (p : ℕ) [Fact p.Prime] : IsDominant (gPt p) := by
  constructor
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (OO p).subtype).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (OO p).subtype_injective]; exact bot_le)

theorem exists_lift {Z : Scheme.{0}} {N W : Z.Opens} (hN : N ≤ W) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ Z)
    (hy : y (cPt p) ∈ W) (x : Sp (kb p) ⟶ N.toScheme) (hx : x ≫ N.ι = rPt p ≫ y) :
    ∃ y' : Sp (OO p) ⟶ W.toScheme, y' ≫ W.ι = y ∧ x ≫ Z.homOfLE hN = rPt p ≫ y' := by
  have hr : Set.range y ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map y.continuous).mem_open W.isOpen hy
  have hy' : IsOpenImmersion.lift W.ι y hr ≫ W.ι = y := IsOpenImmersion.lift_fac _ _ _
  refine ⟨_, hy', ?_⟩
  rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, hy', hx]

theorem chase {k O N W G P H H' Φ X V : Scheme.{0}} {x : k ⟶ N} {i : N ⟶ W} {h : W ⟶ G} {j : G ⟶ P} [Mono j]
    {r : k ⟶ O} {y' : O ⟶ W} {c₁ : O ⟶ X} {f : X ⟶ V} {κ : V ⟶ P} {c' : k ⟶ H'} {e : H' ⟶ Φ} {s : Φ ⟶ X}
    {q : H' ⟶ H} {g : H ⟶ G} {c : k ⟶ H} (h₁ : x ≫ i = r ≫ y') (h₂ : y' ≫ h ≫ j = c₁ ≫ f ≫ κ)
    (h₃ : r ≫ c₁ = (c' ≫ e) ≫ s) (h₄ : e ≫ s ≫ f ≫ κ = q ≫ g ≫ j) (h₅ : c' ≫ q = c) : x ≫ i ≫ h = c ≫ g := by
  rw [← cancel_mono j]
  simp only [Category.assoc] at h₃ ⊢
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, h₄, reassoc_of% h₅]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}

theorem mem_ker (t : ρ.GeoTest p y₀) {a : S.Gam} (ha : a ∈ t.l.yy.ker) : a ∈ t.τ.yy.ker := by
  obtain ⟨e, -, he⟩ := t.mt
  have := (he a 0).2 (by rw [map_zero]; exact ha)
  exact this

theorem integral_eq_section {Q : Clos ρ M U₀ EE} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u} (tm : Q.TMap t c)
    {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.toScheme} (hh : h ≫ Q.G.ι ≫ Q.P.hom = W.ι)
    (hgen : ∀ (x : Sp (PadicAlgCl p) ⟶ W.toScheme) (x' : Sp (PadicAlgCl p) ⟶ pullback ρ.P.A.hom Q.u₀),
      x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι →
      x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀)
    {y' : Sp (OO p) ⟶ W.toScheme} (hy : y' ≫ W.ι = y) {c₁ : Sp (OO p) ⟶ t.u.G.left} {a' : t.u.PtC}
    (h₁ : c₁ ≫ t.u.G.hom = spMap t.u.j) (h₂ : gPt p ≫ c₁ = t.u.toG a')
    (h₃ : t.u.toA a' = spMap y₀ ≫ (ρ.pt a).left) :
    y' ≫ h ≫ Q.G.ι = c₁ ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
  have := Q.proper
  have := isDominant_gPt p
  have e : gPt p ≫ spMap t.u.j = jFK (R := t.u.V) (PadicAlgCl p) ≫ jK t.u.V := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e₀ : jFK (R := t.u.V) (PadicAlgCl p) ≫ spMap t.u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap t.u.fac)
    rw [← Spec.map_comp]
    rfl
  let α : Sp (PadicAlgCl p) ⟶ pullback t.u.G.hom (jK t.u.V) := a'.left
  have ha : α ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) := Over.w a'
  have hs : (α ≫ tm.φ) ≫ pullback.snd _ _ = jFK (R := t.u.V) (PadicAlgCl p) ≫ c.yK := by
    rw [Category.assoc, tm.φ_snd, ← Category.assoc, ha]
  refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ (gPt p) ?_
  · simp only [Category.assoc]
    rw [hh, hy, tm.f_over, ← Category.assoc, h₁, c.fac]
  · have k := hgen (gPt p ≫ y') (α ≫ tm.φ) ?_ ?_
    · rw [Category.assoc, Category.assoc, tm.φ_f] at k
      rw [k, ← Category.assoc (gPt p), h₂]
      exact (Category.assoc _ _ _).symm
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, hy, c.yK_fac, ← Category.assoc, ← e,
        Category.assoc, c.fac]
    · rw [← Category.assoc (α ≫ tm.φ), hs, Category.assoc, Category.assoc, tm.φ_fst, ← Category.assoc c.yK, c.yK_u,
        ← Category.assoc (jFK _), e₀]
      exact h₃

theorem torsSec : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.TorsSec (S.r * S.N) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG hF z _
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  choose W h hz hh hgen using fun a : S.HH M z => _root_.GlobalTheory.ZH.TorsionSection.exists_section hL o Ω S ρ M U₀ EE hB Q z a.1 a.2
  let N : M.Z.Opens := ⟨⋂ a, (W a : Set M.Z), isOpen_iInter_of_finite fun a => (W a).isOpen⟩
  have hN : ∀ a, N ≤ W a := fun a w hw => Set.mem_iInter.1 hw a
  refine ⟨N, Set.mem_iInter.2 hz, ?_⟩
  intro p _ y τ x c hy hx hc
  have hcl := cl_of_test τ
  obtain ⟨y₀, t, cf, ⟨tm⟩⟩ := (_root_.GlobalTheory.ZH.exists_geoTest_tMap_and_centre hL o Ω S ρ M U₀ EE hB Q hS hG).1 p y hcl
  obtain ⟨e, he, hef⟩ := _root_.GlobalTheory.ZH.exists_iso_special_fibre_of_test hL o Ω S ρ M U₀ EE hB Q ex p y y₀ t cf tm τ hS hF
  obtain ⟨c', hc', hcl'⟩ := exists_torsion_pullback τ.H _ c _ hc
  have hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a => by
    rw [cf.at_]
    exact RatModel.norm_val_le_one rfl ((M.O _).algebraMap_mem a)
  have hX : (c' ≫ e.hom) ^ (S.r * S.N) = 1 := by
    rw [← MonObj.pow_comp, hc', MonObj.one_comp]
  obtain ⟨a, ha, c₁, a', h₁, h₂, h₃, h₄⟩ :=
    (special_torsion_eq_reduction hL o Ω S ρ p y₀ t.u t.l t.σ t.cls t.mod hint).2.1 (c' ≫ e.hom) hX
  have haH : a ∈ S.HH M z := by
    rw [hB.atTest z p y y₀ t.τ ⟨hy, hcl⟩ cf.at_]
    exact mem_ker t ha
  let b : S.HH M z := ⟨a, haH⟩
  obtain ⟨y', hy', hxy⟩ := exists_lift (Z := M.Z) (hN b) y ((congrArg (· ∈ W b) hy).mpr (hz b)) x hx
  have key := integral_eq_section tm (hh b) (hgen b _) hy' h₁ h₂ h₃
  refine ⟨M.Z.homOfLE (hN b) ≫ h b, ?_, chase (j := Q.G.ι) hxy key h₄ hef hcl'⟩
  show (M.Z.homOfLE (hN b) ≫ h b) ≫ Q.G.ι ≫ Q.P.hom = N.ι
  rw [Category.assoc, hh, Scheme.homOfLE_ι]

end GlobalTheory.ZH.TorsionValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.GenericFibre

theorem lbIso_pull {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem unif_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) :
    IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) ∧
      LBIso P.A.L (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) ∧
      (letI := H.starRing; ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
        P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act a).left) := by
  letI := H.starRing
  have := P.U.gen_hom
  refine ⟨?_, ?_, fun a => ?_⟩
  · have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  · have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hext : LBIso (P.A.L.pull P.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := by
      have h := P.U.ext
      rw [P.bundle] at h
      exact h
    have h1 : LBIso (P.A.L.pull (P.U.gen.inv.left ≫ P.U.gen.hom.left))
        (t.PP.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullSame P.A.L _ (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left fun _ => rfl)
        (Geo.Tor.chartPullSame t.PP.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left fun _ => rfl) hext
    exact LBIso.chartPull (Geo.Tor.chartPullUnpull P.A.L _ hgi)
      (Geo.Tor.chartPullSame t.PP.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  · have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem fibre_eq_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (χ : Sp R ⟶ Y.X) (m : SABMap t Y.t χ) (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (y : Sp F ⟶ Xo.XF c), y ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ → ∀ (o : Full D F) (φ₀ : o.P.A.left ⟶ Y.oF.t.G.left), IsGrpPullback o.P.A Y.oF.t.G y φ₀ → LBIso o.P.L (Y.oF.t.PP.L.pull φ₀) → (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ₀ = φ₀ ≫ (Y.oF.t.act.act x).left) → ∃ φ : o.P.A.left ⟶ P.A.A.left, IsGrpPullback o.P.A P.A.A (jFK (R := R) F) φ ∧ LBIso o.P.L (P.A.L.pull φ) ∧ (letI := H.starRing; ∀ x, (o.oa.act x).left ≫ φ = φ ≫ (P.oA.act x).left) ∧ φ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ m.φ = φ₀ ≫ Y.m.φ := by
  intro E _ _ _ H D l Xo c O _ β Y R _ _ I t χ m P F _ _ y hy o φ₀ hφ₀ hL₀ ha₀
  letI := H.starRing
  obtain ⟨g₁, l₁, a₁⟩ := unif_generic P
  set ψ := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hψ
  have g₂ : IsGrpPullback P.A.A Y.t.G (jK R ≫ χ) (ψ ≫ m.φ) := g₁.comp m.cart
  have g₃ : IsGrpPullback o.P.A Y.t.G (jFK (R := R) F ≫ jK R ≫ χ) (φ₀ ≫ Y.m.φ) :=
    (hφ₀.comp Y.m.cart).congr hy rfl
  have w₁ : (φ₀ ≫ Y.m.φ) ≫ Y.t.G.hom = (o.P.A.hom ≫ jFK (R := R) F) ≫ jK R ≫ χ :=
    g₃.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨φ, e₁, e₂⟩ : ∃ φ : o.P.A.left ⟶ P.A.A.left, φ ≫ ψ ≫ m.φ = φ₀ ≫ Y.m.φ ∧
      φ ≫ P.A.A.hom = o.P.A.hom ≫ jFK (R := R) F :=
    ⟨g₂.1.lift _ _ w₁, g₂.1.lift_fst _ _ _, g₂.1.lift_snd _ _ _⟩
  have lm : LBIso t.PP.L (Y.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have lY : LBIso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ) := by
    obtain ⟨w, hw, -⟩ := Y.m.lin
    exact ⟨w, hw⟩
  have l₂ : LBIso P.A.L (Y.t.PP.L.pull (ψ ≫ m.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) l₁ (lbIso_pull lm ψ rfl)
  have l₃ : LBIso o.P.L (Y.t.PP.L.pull (φ₀ ≫ Y.m.φ)) :=
    LBIso.trans o.P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL₀ (lbIso_pull lY φ₀ rfl)
  refine ⟨φ, g₂.cancel (g₃.congr rfl e₁.symm) e₂,
    LBIso.trans o.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB P.A.isLB _) l₃ (lbIso_pull l₂ φ e₁.symm).symm,
    fun x => g₂.1.hom_ext ?_ ?_, ?_⟩
  · have a₂ : (P.oA.act x).left ≫ ψ = ψ ≫ (t.act.act x).left := (a₁ x).trans (Category.assoc _ _ _).symm
    have a₃ : (P.oA.act x).left ≫ ψ ≫ m.φ = (ψ ≫ m.φ) ≫ (Y.t.act.act x).left := by
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m.φ) a₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (ψ ≫ ·) (m.act x)).trans (Category.assoc _ _ _).symm)))
    have a₄ : (o.oa.act x).left ≫ φ₀ ≫ Y.m.φ = (φ₀ ≫ Y.m.φ) ≫ (Y.t.act.act x).left := by
      rw [← Category.assoc, ha₀ x, Category.assoc, Category.assoc]
      exact congrArg _ (Y.m.act x)
    rw [Category.assoc, e₁, a₄, Category.assoc φ, a₃, ← Category.assoc φ, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w, e₂, ← Category.assoc, Over.w]
  · rw [← e₁, hψ, Category.assoc]

end GlobalTheory.Ex.GenericFibre
end


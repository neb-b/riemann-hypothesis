module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorusPerp

section Pairing
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.TorusWeight GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem weilQkIs_tor (hG : GlobalFnsSt) {k : ℕ} (p p' : QkPt D F k) {τ : Multiplicative D.X →* Fˣ} (hy : p.y = 0)
    (hτ : IsTor τ p.g) : WeilQkIs D F k p p' (τ (Multiplicative.ofAdd p'.y)).val := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  rw [phiRel_iff hG _ _ hw'] at h₁ h₄
  rw [phiRel_iff hG _ _ hw] at h₂ h₃
  have tr : DegPre.trPt D F p.g.b = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.id_comp]; exact tr_fst D F _
    · rw [Category.id_comp]
      refine (tr_pr D F _).trans ?_
      rw [hτ.1, MonObj.comp_one, _root_.mul_one]
  have v : ∀ (α : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
      (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val =
        gs (ρ ≫ fst _ _).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd α)).val) *
          (val w (ρ ≫ fst _ _).left z J).val := by
    intro α T ρ z J hJ
    have C : IsCub (th D z J) := isCub_cubV D.cub hJ
    have hu : uVal D F k α p.g.b ρ z J = 1 := by
      rw [uVal, hτ.1]
      simp only [MonObj.comp_one]
      unfold cubN
      simp only [C.face₃, C.face₂, Finset.prod_const_one, inv_one, _root_.mul_one]
    have e := val_const (p.g.s α) _ (hτ.2 α) (ρ ≫ fst _ _).left z hJ
    rw [hu, _root_.one_mul, val_mul hJ, Units.val_mul, e]
  intro β
  obtain ⟨α, rfl⟩ : ∃ α, α + p'.y = β := ⟨β - p'.y, sub_add_cancel _ _⟩
  refine (sval_const _ _ _ _).2 fun T ρ z J hJ => ?_
  have e₁ := h₁ α _ rfl T ρ z J hJ
  have e₂ := h₂ (α + p'.y) (α + p'.y) (by rw [hy, add_zero]) T ρ z J hJ
  have e₃ := h₃ α α (by rw [hy, add_zero]) T (ρ ≫ DegPre.trPt D F p'.g.b) z J hJ
  have e₄ := h₄ α _ rfl T ρ z J hJ
  rw [v _ T _ z J hJ, tr, Category.comp_id] at e₂ e₃
  rw [Category.assoc, tr_fst] at e₃
  rw [e₂, e₄, e₃, e₁, ofAdd_add, map_mul, Units.val_mul (τ _), map_mul, gs_mul _ _ ⊤ trivial]
  ring


attribute [local instance] gtGroup in
theorem exists_qkPt_tor (hB : D.TauBimult) {k : ℕ} (τ : Multiplicative D.X →* Fˣ) (h : τ ^ k = 1) :
    ∃ p : QkPt D F k, p.y = 0 ∧ IsTor τ p.g :=
  ⟨qkMk hB 0 (torusPt D F (Additive.ofMul τ)) (by rw [← map_nsmul, ← ofMul_pow, h, ofMul_one, map_zero, map_zero]),
    rfl, (isTor_iff _ _).2 (isTorusPtF_torusPt τ)⟩

end Pairing

section Algebra

theorem eStd_add_left (g n : ℕ) (a a' b : Fin g ⊕ Fin g → ZMod n) :
    eStd g n (a + a') b = eStd g n a b + eStd g n a' b := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eStd_add_right (g n : ℕ) (a b b' : Fin g ⊕ Fin g → ZMod n) :
    eStd g n a (b + b') = eStd g n a b + eStd g n a b' := by
  simp only [eStd, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_eStd (g n : ℕ) (a : Fin g ⊕ Fin g → ZMod n) (h : ∀ b, eStd g n a b = 0) : a = 0 := by
  funext j
  rcases j with i | i
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inr i) 1)
  · simpa [eStd, Pi.single_apply] using h (Pi.single (.inl i) 1)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem isoFree_perp_ker {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (yy : S.Gam →+ X ⧸ (nsmulAddMonoidHom (S.r * S.N) : X →+ X).range) (hs : Function.Surjective yy)
    (H : ∀ l : X →+ ZMod (S.r * S.N), ∃ a ∈ yy.ker, ∀ b α, yy b = QuotientAddGroup.mk α → eStd S.g _ a b = l α) :
    S.IsoFree (S.perp yy.ker) ∧ ∃ wt : X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : X),
      yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker,
        wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  choose σ hσ using fun α : X => hs (QuotientAddGroup.mk α)
  have ind : ∀ (t : S.perp yy.ker) (b b' : S.Gam), yy b = yy b' → eStd S.g _ t b = eStd S.g _ t b' := by
    intro t b b' e
    have h0 : eStd S.g _ t (b - b') = 0 := t.2 _ (by rw [AddMonoidHom.mem_ker, map_sub, e, sub_self])
    rw [← sub_add_cancel b b', eStd_add_right, h0, zero_add]
  let Λ : S.perp yy.ker →+ X →+ ZMod (S.r * S.N) := AddMonoidHom.mk'
    (fun t => AddMonoidHom.mk' (fun α => eStd S.g _ t (σ α)) fun α β => by
      rw [← eStd_add_right]
      exact ind t _ _ (by rw [map_add (f := _), hσ, hσ, hσ, QuotientAddGroup.mk_add]))
    fun t t' => AddMonoidHom.ext fun α => eStd_add_left _ _ _ _ _
  have hΛ : ∀ (t : S.perp yy.ker) b α, yy b = QuotientAddGroup.mk α → Λ t α = eStd S.g _ t b :=
    fun t b α e => ind t _ _ ((hσ α).trans e.symm)
  have hbij : Function.Bijective Λ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => Subtype.ext (eq_zero_of_eStd _ _ _ fun b => ?_), fun l => ?_⟩
    · obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy b)
      rw [← hΛ t b α e.symm, ht, AddMonoidHom.zero_apply]
    · obtain ⟨a, -, ha⟩ := H l
      exact ⟨⟨a, fun h hh => (ha h 0 hh).trans (map_zero l)⟩, AddMonoidHom.ext fun α => ha _ _ (hσ α)⟩
  refine ⟨⟨fun s hs t ht => ?_, Module.finrank ℤ X, ⟨(AddEquiv.ofBijective Λ hbij).trans
    ((addMonoidHomLequivInt ℤ).toAddEquiv.trans ((Module.finBasis ℤ X).constr ℤ).symm.toAddEquiv)⟩⟩,
    Λ.flip.compr₂ (ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom, fun x α e t => ?_⟩
  · obtain ⟨a, ha, hl⟩ := H (Λ ⟨s, hs⟩)
    obtain ⟨α, e⟩ := QuotientAddGroup.mk_surjective (yy t)
    rw [← hΛ ⟨s, hs⟩ t α e.symm, ← hl t α e.symm, GlobalTheory.ThetaProj.eStd_swap, ht a ha, neg_zero]
  · rw [← hΛ t x α e]; rfl

end Algebra

section Points

def ptHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm

theorem ptHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (ptHom h T) :=
  ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm)),
    fun z => ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem map_unitOn {A B : Type} [CommRing A] [CommRing B] (β : A →+* B) (c : Aˣ) :
    Units.map (spMap β).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map β.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem unitOn_injective {K : Type} [CommRing K] : Function.Injective (unitOn (R := K)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1 (congrArg Units.val h))

end Points

theorem isoFree_perp_and_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  intro hL _ hT o Ω _ _ _ hA S ρ p _ y₀ u yy hs hyy
  have hG := hL.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have := ρ.P.isAb.comm
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (PadicAlgCl p)ˣ := Units.map y₀.toMonoidHom c₀
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map (y₀.comp (algebraMap o S.R))

  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))
  have hΦ : Function.Bijective Φ := ptHom_bijective _ _
  have lab : ∀ a q, Φ (f q) = h ≫ ρ.pt a → yy a = QuotientAddGroup.mk q.y := fun a q e =>
    hyy a q _ ((f₁ _ _).2 rfl) ((congrArg (fun z => z.left) e).trans (by rw [← hh]; rfl))
  let pt : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A) := MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun _ _ => ρ.pt_add _ _
  have onto : ∀ b, ∃ q, Φ (f q) = h ≫ ρ.pt b := fun b => by
    obtain ⟨x, hx⟩ := hΦ.2 (h ≫ ρ.pt b)
    obtain ⟨q, rfl⟩ := f₂ x (hΦ.1 (by
      have e : ρ.pt b ^ (S.r * S.N) = 1 := by
        refine (map_pow pt (Multiplicative.ofAdd b) _).symm.trans ?_
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul, ofAdd_zero, map_one]
      rw [map_pow, hx, map_one, ← MonObj.comp_pow, e, MonObj.comp_one]))
    exact ⟨q, hx⟩
  have weil : ∀ a b q q', Φ (f q) = h ≫ ρ.pt a → Φ (f q') = h ≫ ρ.pt b →
      WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (f q) (f q') (unitOn (ω ^ (eStd S.g _ a b).val)) := fun a b q q' e e' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil a b (c₀ ^ (eStd S.g _ a b).val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← e, ← e'] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _
      (Φ (f q)) (Φ (f q')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  refine isoFree_perp_ker S yy hs fun l => ?_
  let χ := AddChar.zmodChar (S.r * S.N) hω.pow_eq_one
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ := χ.toMonoidHom.comp l.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (l α).val := fun _ => rfl
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) (k := S.r * S.N) u.D.tau_bimult τ (MonoidHom.ext fun α => by
    show (ω ^ (l α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ (Φ (f q)) (by rw [← map_pow, hq1, map_one])
  refine ⟨a, (lab a q ha.symm).trans (by rw [hq]; rfl), fun b α e => ?_⟩
  obtain ⟨q', hq'⟩ := onto b
  have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a b q q' ha.symm hq')
    ((f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)))
  rw [hτ] at e₁
  rw [ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)]
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 ((lab b q' hq').symm.trans e)
  have hz' : (S.r * S.N) • z = -q'.y + α := hz
  have := congrArg l hz'
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_add (f := _), map_neg] at this
  exact neg_add_eq_zero.1 this.symm

end GlobalTheory.ZH.TorusPerp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymBaseChange

variable {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G'] {f : B' ⟶ B} {φ : G'.left ⟶ G.left}

theorem pushPt_injective (h : IsGrpPullback G' G f φ) {T : Over B'} {x y : T ⟶ G'}
    (e : pushPt h.1.w x = pushPt h.1.w y) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_endo (h : IsGrpPullback G' G f φ) (w : G ⟶ G) [IsMonHom w] :
    ∃ w' : G' ⟶ G', IsMonHom w' ∧ ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := by
  let w' : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ w.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have hw : w'.left ≫ φ = φ ≫ w.left := h.1.lift_fst _ _ _
  have pa : ∀ {T : Over B'} (x : T ⟶ G'), pushPt h.1.w (x ≫ w') = pushPt h.1.w x ≫ w := fun x =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hw, Category.assoc])
  have mul : ∀ (T : Over B') (x y : T ⟶ G'), (x * y) ≫ w' = (x ≫ w') * (y ≫ w') := by
    intro T x y
    apply pushPt_injective h
    have a : pushPt h.1.w (x * y) = pushPt h.1.w x * pushPt h.1.w y := map_mul (pushHom h T) x y
    have b : pushPt h.1.w ((x ≫ w') * (y ≫ w')) = pushPt h.1.w (x ≫ w') * pushPt h.1.w (y ≫ w') :=
      map_mul (pushHom h T) _ _
    rw [pa, a, b, pa, pa, MonObj.mul_comp]
  refine ⟨w', ⟨?_, ?_⟩, pa⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over B') ⟶ G') ≫ w' = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul (G' ⊗ G') (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem hypS_baseChange : ∀ (B B' : Scheme.{0}) (G : Over B) (G' : Over B') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (f : B' ⟶ B) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → HypS G L → HypS G' L' := by
  intro B B' G G' _ _ _ _ f φ L L' hL hL' h hb ⟨w, wd, hw, hwd, hs, hp, ha⟩
  obtain ⟨w', hw', pa⟩ := exists_endo h w
  obtain ⟨wd', hwd', pd⟩ := exists_endo h wd
  have hB : (L.pull φ).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (φ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 G'.left) y _ hy, map_one, gm_pull_g L φ (𝟙 G'.left) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 G'.left) y _ hy, gm_res (𝟙 G'.left) y _ hy,
        gm_res (𝟙 G'.left) y _ hy, gm_pull_g L φ (𝟙 G'.left) y I J hy.1.1 hy.1.2,
        gm_pull_g L φ (𝟙 G'.left) y J K hy.1.2 hy.2, gm_pull_g L φ (𝟙 G'.left) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  refine ⟨w', wd', hw', hwd', ?_, ?_, ?_⟩
  · apply pushPt_injective h
    have b : pushPt h.1.w (w' * wd') = pushPt h.1.w w' * pushPt h.1.w wd' := map_mul (pushHom h G') _ _
    have c := pa (𝟙 G')
    have d := pd (𝟙 G')
    rw [Category.id_comp] at c d
    rw [b, c, d, ← MonObj.comp_mul, hs, Category.comp_id]
  · have h₁ : LBIso (L.pull φ) (cubeLB G' ![𝟙 G', w'] (L.pull φ)) := by
      let U := pushPt h.1.w (𝟙 G')
      refine LBIso.chartPull (chartPullPull L _ U.left (Category.id_comp _))
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _)) I.down) hp
    have h₂ : LBIso (cubeLB G' ![𝟙 G', w'] (L.pull φ)) (cubeLB G' ![𝟙 G', w'] L') :=
      GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _
    exact LBIso.trans hL' hB (DVR.linComb_isLB L' hL' _ _) hb
      (LBIso.trans hB (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁ h₂)
  · have h₁ : LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] (L.pull φ))
        (cubeLB G' ![fst G' G', snd G' G' ≫ wd'] (L.pull φ)) := by
      let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
      refine LBIso.chartPull (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
        fin_cases i
        · exact (pa _).trans (by simp [U])
        · simp [U]) I.down)
        (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
          fin_cases i
          · simp [U]
          · exact (pd _).trans (by simp [U])) I.down) ha
    exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hb _ _)
      (LBIso.trans (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB _ hB _ _) (DVR.linComb_isLB L' hL' _ _) h₁
        (GlobalTheory.PowPrimitive.lbIso_linComb hb.symm _ _))

end GlobalTheory.SymBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FrAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsComb {k : ℕ} {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) : Prop :=
  ∀ j, σ.f j = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b l)) * (t l).f j
end
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

structure ThetaSys.Real.UTest.Geom (u : ρ.UTest p y₀) where
  pt : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
  pt_over : ∀ a, (pt a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left
  pt_add : ∀ a b, pt (a + b) = pt a * pt b
  pt_bij : ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃! a, pt a = z
  weil : ∀ a b (c : (PadicAlgCl p)ˣ),
    (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) →
    WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (pt a) (pt b) (unitOn c)
  rig : LB.Gen (u.A.L.pull (eSec u.A.A))
  rig_gen : rig.IsGen
  fr : ∀ a, FrAt (pt a)
  fr_tors : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (pt a) (fr a)
  th : SecA u.A (PadicAlgCl p) 1
  th_val : ∀ a, ValAt th (pt a) (fr a) (y₀ ⟨S.th a, S.th_mem a⟩)
  s : S.J → SecA u.A (PadicAlgCl p) S.N
  ev_val : ∀ a i, ValAt (s i) (pt a) (fr a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)
  α : LB.Gen (LB.LinComb u.A.L (K := Fin 2) ![(snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A).left,
    (snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -((1 : ℕ) : ℤ)])
  α_gen : α.IsGen
  α_norm : LB.Gen.Corr u.A.L _ _ _ _ (LB.pullGen u.A.L _ _ α (ptSecT u.A.A 1).left)
    (rigT u.A.A u.A.L rig (TFK (R := u.V) (PadicAlgCl p)) ((S.N : ℤ) - 1))
  s_zero : IsTwistPull u.A.A u.A.L (mulT u.A.A _ (ρ.n ^ ρ.k)) (snd _ u.A.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _)
    (S.N : ℤ) ((1 : ℕ) : ℤ) α th (s ρ.i₀)
  U : S.Gam → ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  U_sym : ∀ a, SymLift u.A.A u.A.L S.N S.N (pt (S.r • a)) (U a)
  U_act : ∀ a i σ, IsActOf u.A.A u.A.L S.N (U a) (s i) σ ↔ IsComb s (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) σ

def NormVal {p : ℕ} [Fact p.Prime] (π : PadicAlgCl p) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) : Prop :=
  0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ (x : PadicAlgCl p) (q : ℚ), v x = (q : WithTop ℚ) ↔ ‖x‖ = ‖π‖ ^ (q : ℝ)
end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PointDescendsToValuationRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem mem_range_of_dominating {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {W C : Type} [CommRing W]
    [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C) (hα : IsLocalHom α)
    (hβ : Function.Injective β) (hc : β.comp α = ga.comp (algebraMap V (FractionRing V)))
    (a : FractionRing V) (w : W) (h : β w = ga a) : a ∈ (algebraMap V (FractionRing V)).range := by
  rcases ValuationRing.isInteger_or_isInteger V a with ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨v, hv⟩
  · by_cases ha : a = 0
    · exact ha ▸ Subring.zero_mem _
    have h1 : β (α v) = ga a⁻¹ := by rw [← hv]; exact congrArg (· v) (congrArg DFunLike.coe hc)
    have h2 : α v * w = 1 := hβ (by rw [map_mul, h1, h, ← map_mul, inv_mul_cancel₀ ha, map_one, map_one])
    obtain ⟨u, rfl⟩ := hα.map_nonunit v (IsUnit.of_mul_eq_one _ h2)
    refine ⟨(u⁻¹ : Vˣ), ?_⟩
    rw [← inv_inv a, ← hv]
    exact map_units_inv _ u

theorem point_descends_to_valuationRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x := by
  intro V _ _ _ W C _ _ _ α β ga hα hβ hc X y x hxy
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (IsLocalRing.closedPoint W)) trivial
  have hy : ⊤ ≤ y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of W) y hp).ge
  have hx : ⊤ ≤ x ⁻¹ᵁ U := by
    intro p _
    have h1 : (spMap β ≫ y) (IsLocalRing.closedPoint C) ∈ U := hy (x := spMap β _) trivial
    rw [hxy] at h1
    obtain rfl : p = spMap ga (IsLocalRing.closedPoint C) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) _ _
    exact h1
  have key : ∀ f, β (valR y U f) = ga (valR x U f) := fun f => by
    rw [← HolHom.valR_spMap β y U hy, ← HolHom.valR_spMap ga x U hx, hxy]
  have hinj := IsFractionRing.injective V (FractionRing V)
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let φ : Γ(X, U) →+* V := e.symm.toRingHom.comp ((HolHom.evalHom x U hx).codRestrict _ fun f =>
    mem_range_of_dominating α β ga hα hβ hc _ _ ((key f).trans (by rw [HolHom.valR_eq _ _ hx])))
  have hφ : ∀ f, algebraMap V (FractionRing V) (φ f) = valR x U f := fun f => by
    rw [HolHom.valR_eq _ _ hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  let h : Sp V ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hh : ⊤ ≤ h ⁻¹ᵁ U := fun p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hval : ∀ f, valR h U f = φ f := fun f => by
    rw [HolHom.valR_eq _ _ hh]
    exact congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom φ) hh)
  refine ⟨h, HolHom.point_ext hU (fun p _ => hh (x := spMap α p) trivial) hy fun f => ?_,
    HolHom.point_ext hU (fun p _ => hh (x := jK V p) trivial) hx fun f => ?_⟩
  · rw [HolHom.valR_spMap _ _ _ hh, hval]
    refine hβ ?_
    rw [key, ← hφ]
    exact congrArg (· (φ f)) (congrArg DFunLike.coe hc)
  · exact (HolHom.valR_spMap (algebraMap V (FractionRing V)) _ _ hh f).trans (by rw [hval, hφ])

end GlobalTheory
end


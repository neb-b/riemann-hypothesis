module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjectiveOfLaws
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.LevelCover

namespace GlobalTheory.LevCover

private theorem levStrRep_lemma (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [Field B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hpq : 1 ≤ D.p + D.q) (l₂ : Level H) (b₂ : Base l₂ B) (hd : l.Dvd l₂)
    (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) :
    ∃ (V : Over S) (χ θ : D.La → (V ⟶ o.t.G)), IsFinite V.hom ∧ Etale V.hom ∧ Surjective V.hom ∧
      LevStr o b₂ V χ θ ∧
      (∀ (T : Over S) (u u' : T ⟶ V), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
        ∃ h : T ⟶ V, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have hsim := SimAlg.sim_group E H D hpq
  obtain ⟨hfree, hfin⟩ := datum_free D
  refine exists_levStr_rep o l₂ b₂ hd hζ (fun g n k hn hk => hsim.1 g n k hn hk)
    (fun N f ν => exists_sim_lift E H D N f ν)
    (fun l' N ν => SimMult.exists_sim_trivial_of_mult SimAlg.sim_group exists_sim_lift E H D l' N ν) ?_ ?_
  · intro n hn
    have hu : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
      simpa using (b.unit n hn).map (fnOn s)
    obtain ⟨Z, et, hZ⟩ :=
      exists_finiteEtale_latticeTorsionHom S o.t.G n D.La (ObjDim.isAbelianScheme o) hu
    exact ⟨Z, et, hZ⟩
  · intro N _ T x y c hN hx hy hc
    exact PairingLocus.exists_clopen_of_isLocallyNoetherian hL S (GlobalTheory.Obj.toPolAV o) N T x y c hN hx hy hc

private theorem weilIs_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T' : Over S') (k : ℤ) (x y : T' ⟶ t'.G)
    (x₀ y₀ : Over.mk (T'.hom ≫ f) ⟶ t.G) (c : Γ(T'.left, ⊤)ˣ) (h₁ : x₀.left = x.left ≫ m.φ)
    (h₂ : y₀.left = y.left ≫ m.φ) : Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ c :=
  weilIs_grpPullback_of_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart (sabMap_lbIso m)
    T' k x y x₀ y₀ c h₁ h₂

private theorem lieMult_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (k : Type) [Field k] (x : Sp k ⟶ S')
    (τ : 𝓞 E →+* k) (n : ℕ) : LieMult t'.act x τ n ↔ LieMult t.act (x ≫ f) τ n :=
  LiePull.lieMult_pull (𝓞 E) S S' t.G t'.G f m.φ t.act t'.act m.cart m.act k x τ n

theorem levelCover_noetherian (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsLocallyNoetherian S → 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o hS hpq hd hρ hζ
  have := hS
  obtain ⟨V, χ, θ, hVf, hVe, hVs, hlev, hext, hex⟩ := levStrRep_lemma hL o hpq l₂ b₂ hd hζ
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l B B b b (RingHom.id B) S V.left s (V.hom ≫ s) V.hom rfl rfl
    (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨o₂, m, hm, hχ, hθ⟩ := obj_of_levStr o hρ V o₁.t n₁.toSABMap (weilIs_iff_of_sabMap n₁.toSABMap)
    (fun k _ x τ n => lieMult_iff_of_sabMap n₁.toSABMap k x τ n) o₁.ample o₁.ktriv hlev
  refine ⟨V.left, V.hom, o₂, m, hVf, hVe, hVs, hm, ?_⟩
  intro T f o' m' hc
  obtain ⟨χ', θ', hlev', hχ', hθ'⟩ := levStr_of_obj o (Over.mk f) o' m' (weilIs_iff_of_sabMap m') hc.1 hc.2
  obtain ⟨g, hgχ, hgθ⟩ := hex (Over.mk f) χ' θ' hlev'
  have hg : g.left ≫ V.hom = f := by simpa using Over.w g
  obtain ⟨u, hu⟩ := sab_cancel m m' g.left hg

  have key : ∀ a, ((o'.eta a).left ≫ m'.φ = g.left ≫ (o₂.eta a).left ≫ m.φ) ∧
      ((o'.etaA a).left ≫ m'.φ = g.left ≫ (o₂.etaA a).left ≫ m.φ) := fun a => by
    constructor
    · rw [← hχ' a, ← hgχ a, Over.comp_left, hχ a]
    · rw [← hθ' a, ← hgθ a, Over.comp_left, hθ a]
  have hη : ∀ a, (o'.eta a).left ≫ u.φ = g.left ≫ (o₂.eta a).left := fun a =>
    sec_cancel u m (o'.eta a) (o₂.eta a) (by rw [hu]; exact (key a).1)
  have hηA : ∀ a, (o'.etaA a).left ≫ u.φ = g.left ≫ (o₂.etaA a).left := fun a =>
    sec_cancel u m (o'.etaA a) (o₂.etaA a) (by rw [hu]; exact (key a).2)
  refine ⟨g.left, ⟨hg, ⟨u, hη, hηA⟩, hu⟩, ?_⟩
  rintro h' ⟨hh', ⟨u', hu₁, hu₂⟩, hu'⟩
  have hu'' : u'.cm.F ≫ m.φ = m'.φ := hu'
  have hgg : (Over.homMk h' hh' : Over.mk f ⟶ V) = g := by
    apply hext
    · intro a
      ext1
      simp only [Over.comp_left, hχ a, Over.homMk_left]
      rw [← (key a).1, ← Category.assoc, ← hu₁ a, Category.assoc, hu'']
    · intro a
      ext1
      simp only [Over.comp_left, hθ a, Over.homMk_left]
      rw [← (key a).2, ← Category.assoc, ← hu₂ a, Category.assoc, hu'']
  rw [← hgg]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem levelMap_over_field_noetherian (hL : Out.Laws)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  have hsm0 : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hsm0₂ : Smooth Xo₂.s := by
    have := Xo₂.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo₂.s
  have hsmX : Smooth (pullback.snd Xo.s (spMap j)) := inferInstance
  have hsmX₂ : Smooth (pullback.snd Xo₂.s (spMap j₂)) := inferInstance
  obtain ⟨rX, -, nX⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX
  obtain ⟨rX₂, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX₂

  obtain ⟨o, ⟨no⟩⟩ := obj_pull E H D l (KA l) F (baseKA l) b j Xo.X (pullback Xo.s (spMap j)) Xo.s
    (pullback.snd _ _) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨no₂⟩⟩ := obj_pull E H D l₂ (KA l₂) F (baseKA l₂) b₂ j₂ Xo₂.X (pullback Xo₂.s (spMap j₂)) Xo₂.s
    (rF ≫ pullback.snd _ _) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  have hno1 : ∀ a, (o.eta a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.eta a).left := no.2
  have hno2 : ∀ a, (o.etaA a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.etaA a).left := no.3
  have hno₂1 : ∀ a, (o₂.eta a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.eta a).left := no₂.2
  have hno₂2 : ∀ a, (o₂.etaA a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.etaA a).left := no₂.3
  have hRX : Represents o := represents_pullback ObjMaps.id_comp_cancel Xo j
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo F b j S s o' hS e₁ e₂) rfl o no
  have hRX₂ : Represents o₂ := represents_pullback ObjMaps.id_comp_cancel Xo₂ j₂
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo₂ F b₂ j₂ S s o' hS e₃ e₄) h₂ o₂ no₂

  obtain ⟨Y, π, oc, mc, hπf, hπe, hπs, hmc, huniv⟩ :=
    levelCover_noetherian hL E H D l l₂ F b b₂ _ (pullback.snd Xo.s (spMap j)) o nX hpq hd hρ hζ
  have hsmπ : Smooth π := inferInstance
  have hsmY : Smooth (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
  obtain ⟨rY, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmY
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l F F b b (RingHom.id F) _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) π
    rfl rfl (by rw [spMap_id', Category.comp_id]) o

  obtain ⟨mcomp, hmcomp⟩ := sab_comp no₂.toSABMap m h₁.symm
  obtain ⟨m₂, hm₂'⟩ := sab_cancel no.toSABMap mcomp rF rfl
  have hm₂c : (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m₂.φ = rF ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m₂.φ = rF ≫ (o.etaA a).left) := by
    constructor
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂1 a), Category.assoc, hm₁ a, ← Category.assoc,
        ← h₁, Category.assoc, hno1 a]
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂2 a), Category.assoc, hm₂ a, ← Category.assoc,
        ← h₁, Category.assoc, hno2 a]
  obtain ⟨h, hiso, hπ⟩ := iso_cover ObjMaps.id_comp_cancel (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n₁ m₂ mc hm₂c hmc
    hRX hRX₂ rX₂ rY (obj_rigid_closed hL E H D l F F b b _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) o o₁ π
      (Or.inl rY)) huniv
  rw [← hπ]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

theorem levelMap_finite_etale_surjective_of_laws (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hr c c₂ hc rF h₁ h₂
  obtain ⟨-, -, hm₁, hm₂⟩ := hr
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  dsimp only at hc
  subst hc
  rw [spMap_inclusion_self, Category.comp_id] at h₂
  exact levelMap_over_field_noetherian hL Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    (IntermediateField.inclusion le).toRingHom (IntermediateField.inclusion le₂).toRingHom rfl rfl rfl rfl
    (baseOf_rho l l₂ F le le₂) (baseOf_zeta l l₂ F le le₂ hd.2.2) rF h₁ h₂

end GlobalTheory.LevCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientUnramifiedDualNumberPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelQuotUnram

open GlobalTheory.TangentCrit (dualPt dualBase dualPt_dualBase dualPt_dualBase_assoc)

lemma subsingleton_sp_dual (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ a : PrimeSpectrum (DualNumber k), a.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro a
    ext d
    constructor
    · intro hd
      by_contra h
      exact a.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hd
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 _ h)))
    · intro hd
      have h : d.fst = 0 := hd
      refine a.isPrime.mem_of_pow_mem 2 ?_
      have : d ^ 2 = 0 := by ext1 <;> simp [pow_two, h]
      rw [this]; exact a.asIdeal.zero_mem
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

lemma dualMap_cancel {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}}
    {g g' : Sp (DualNumber k) ⟶ X} (h : spMap (Chart.dualMapR f) ≫ g = spMap (Chart.dualMapR f) ≫ g') : g = g' := by
  have := subsingleton_sp_dual k
  refine TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (Chart.dualMapR f))
    (fun z => ⟨IsLocalRing.closedPoint (DualNumber K), Subsingleton.elim _ _⟩) (fun d hd _ => ?_) h h
  have h₁ : f d.fst = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.fst hd
  have h₂ : f d.snd = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.snd hd
  exact TrivSqZeroExt.ext (f.injective (by simpa using h₁)) (f.injective (by simpa using h₂))

lemma constPt_dualMap {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) :
    constPt (spMap (Chart.dualMapR f) ≫ x) = spMap (Chart.dualMapR f) ≫ constPt x := by
  simp only [constPt, ← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

lemma exists_dual_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [Smooth π] [IsAffineHom π] {k : Type} [Field k]
    (x : Sp (DualNumber k) ⟶ Y) (y : Sp k ⟶ X) (h : y ≫ π = dualPt k ≫ x) :
    ∃ x₂ : Sp (DualNumber k) ⟶ X, dualPt k ≫ x₂ = y ∧ x₂ ≫ π = x := by
  have := subsingleton_sp_dual k
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint (DualNumber k)))) isOpen_univ
  have hx : Set.range x ⊆ U := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint (DualNumber k))]
  refine exists_lift_of_smooth_of_isAffineOpen π hU (hU.preimage π) le_rfl _ x y h hx ?_ ?_
  · rintro _ ⟨z, rfl⟩
    change π (y z) ∈ U
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hx ⟨_, rfl⟩
  · intro R A _ _ _ _ _ _ ρ hρ φ
    refine SmoothNilLift.exists_lift_of_nil ρ (fun c => ⟨TrivSqZeroExt.inl c, hρ _⟩) (fun d hd => ?_) φ
    have h : TrivSqZeroExt.fst d = 0 := (hρ d).symm.trans hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma sab_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

lemma torsion_rigid {X : Scheme.{0}} {k : Type} [Field k] (t : SAB H (Sp (DualNumber k))) (t₂ : SAB H X)
    (y : Sp k ⟶ X) (ν : SABMap t t₂ (dualBase k ≫ y)) {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤)))
    (σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G) (τ : 𝟙_ (Over X) ⟶ t₂.G) (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (h : dualPt k ≫ σ.left ≫ ν.φ = y ≫ τ.left) : σ.left ≫ ν.φ = (dualBase k ≫ y) ≫ τ.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback ν.cart (𝟙 _) (dualBase k ≫ y) (Category.id_comp _).symm
  have h₁ : (e σ).left = σ.left ≫ ν.φ := he σ
  have h₂ : (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ).left = (dualBase k ≫ y) ≫ τ.left := by simp
  rw [← h₁, ← h₂]
  congr 1
  refine GrpTangent.eq_of_tangentMap_injective y (mulN t₂.G n)
    (GrpTangent.tangentMap_pullback_mulN_bijective t₂.G hn y).1 _ _ (Over.OverMorphism.ext ?_) ?_
  · change dualPt k ≫ Over.Hom.left (e σ) = dualPt k ≫ Over.Hom.left (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ)
    rw [h₁, h₂, h, Category.assoc, dualPt_dualBase_assoc]
  · rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← comp_pow, hτ, comp_one, ← map_pow]
    exact (congrArg e hσ).trans (map_one e)

variable {D : Datum H}

section
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)

lemma pow_eq_of_add {L Γ : Type} [AddCommGroup L] [Group Γ] (f : L → Γ) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (a := f 0) (by rw [← this, _root_.mul_one])).symm
  | succ n ih => rw [pow_succ, ih, add_smul, one_smul, hf]

lemma natCast_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

lemma nsmul_mem_Mb (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top

lemma eta_pow (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [pow_eq_of_add o.eta o.eta_add, o.eta_ker _ (nsmul_mem_Mb l a)]

lemma etaA_pow (a : D.La) : o.etaA a ^ l.A = 1 := by
  rw [pow_eq_of_add o.etaA o.etaA_add, o.etaA_ker]

include b s in
lemma isUnit_nat {n : ℕ} (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  simpa using (b.unit n hn).map ((Scheme.ΓSpecIso (.of B)).inv ≫ s.appTop).hom

end

theorem unram_of_isAlgClosed (hL : Out.Laws) {l l₂ : Level H} (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s))
    (m₁ : ObjMap ob Q.univ x) (m₂ : ObjMap ob Q.univ (constPt x)) : x = constPt x := by
  have := Q.fin
  have := Q.etale
  have := Q.onto
  obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective Q.π (dualPt k ≫ x)
  obtain ⟨x₂, hx₂, hx⟩ := exists_dual_lift Q.π x y hy.symm
  have hc : constPt x₂ = dualBase k ≫ y := by rw [← hx₂]; rfl
  have hcπ : (dualBase k ≫ y) ≫ Q.π = constPt x := by rw [Category.assoc, ← hy]; rfl

  obtain ⟨o₀, ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    (dualPt k ≫ x ≫ Q.s) (dualPt k) rfl rfl (by simp [spMap]) ob
  have hr : r.toSABMap.φ ≫ m₁.toSABMap.φ = r.toSABMap.φ ≫ m₂.toSABMap.φ := by
    obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp m₁.toSABMap r.toSABMap
    obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp m₂.toSABMap r.toSABMap
    have e : dualPt k ≫ constPt x = dualPt k ≫ x := dualPt_dualBase_assoc k _
    obtain ⟨n₃, hn₃⟩ := sab_cast n₂ e
    rw [← hn₁, ← hn₂, ← hn₃]
    refine obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ Q.univ o₀ _ (Or.inl inferInstance) n₁ n₃
      fun a => ⟨_, rfl, ?_⟩
    rw [hn₃, hn₂, hn₁, reassoc_of% (r.eta a), reassoc_of% (r.eta a), m₁.eta, m₂.eta, reassoc_of% e]
  have hr' : ∀ {Z : Scheme.{0}} (z : Z ⟶ ob.t.G.left) (w : Z ⟶ Sp k), z ≫ ob.t.G.hom = w ≫ dualPt k →
      z ≫ m₁.toSABMap.φ = z ≫ m₂.toSABMap.φ := by
    intro Z z w hz
    rw [← r.cart.1.lift_fst z w hz, Category.assoc, Category.assoc]
    exact congrArg _ hr

  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l₂ _ _ (baseKA l₂) (baseKA l₂) (RingHom.id _) _ _ Xo₂.s
    (x₂ ≫ Xo₂.s) x₂ rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨a₁, ha₁⟩ := ObjMaps.exists_sab_comp Q.m n₁.toSABMap
  obtain ⟨a₂, ha₂⟩ := sab_cast a₁ (hx.trans (Category.id_comp x).symm)
  obtain ⟨u, hu⟩ := ObjMaps.exists_sab_cancel m₁.toSABMap a₂
  obtain ⟨a₃, ha₃⟩ := ObjMaps.exists_sab_comp m₂.toSABMap u
  obtain ⟨a₄, ha₄⟩ := sab_cast a₃ ((Category.id_comp _).trans hcπ.symm)
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_cancel Q.m a₄
  have e₁ : n₁.toSABMap.φ ≫ Q.m.φ = u.φ ≫ m₁.toSABMap.φ := by rw [← ha₁, ← ha₂, hu]
  have e₂ : n₂.φ ≫ Q.m.φ = u.φ ≫ m₂.toSABMap.φ := by rw [← hn₂, ha₄, ha₃]
  have key : ∀ σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o₁.t.G,
      dualPt k ≫ σ.left ≫ n₂.φ = dualPt k ≫ σ.left ≫ n₁.toSABMap.φ := by
    intro σ
    have hσ : σ.left ≫ o₁.t.G.hom = 𝟙 _ := Over.w σ
    refine Q.m.cart.1.hom_ext ?_ ?_
    · have := hr' (dualPt k ≫ σ.left ≫ u.φ) (𝟙 _) (by
        have w := u.cart.1.w
        simp only [Category.assoc, Category.id_comp, Category.comp_id] at w ⊢
        rw [w, hσ]
        exact Category.comp_id _)
      simp only [Category.assoc] at this ⊢
      rw [e₁, e₂, this]
    · have w₁ := n₁.cart.1.w
      have w₂ := n₂.cart.1.w
      simp only [Category.assoc]
      rw [w₁, w₂, reassoc_of% hσ, reassoc_of% hσ, dualPt_dualBase_assoc, hx₂]
  obtain ⟨n₃, hn₃⟩ := sab_cast n₂ hc.symm
  have h₂ : x₂ = constPt x₂ := by
    refine Xo₂.unram k x₂ o₁ ⟨n₁⟩ ⟨{ toSABMap := n₃, eta := fun a => ?_, etaA := fun a => ?_ }⟩
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) (by have := l₂.three_le; omega))
        _ _ (eta_pow o₁ a) (eta_pow Xo₂.univ a) ?_
      rw [key, n₁.eta, reassoc_of% hx₂]
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) l₂.A_pos)
        _ _ (etaA_pow o₁ a) (etaA_pow Xo₂.univ a) ?_
      rw [key, n₁.etaA, reassoc_of% hx₂]
  rw [← hcπ, ← hc, ← h₂, hx]

end GlobalTheory.LevelQuotUnram

namespace GlobalTheory

theorem levelQuot_unram : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  rintro hL - E _ _ _ H D l l₂ Xo₂ Q - - k _ x ob ⟨m₁⟩ ⟨m₂⟩
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  refine LevelQuotUnram.dualMap_cancel f ?_
  rw [← LevelQuotUnram.constPt_dualMap]
  obtain ⟨o', ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    ((spMap (Chart.dualMapR f) ≫ x) ≫ Q.s) (spMap (Chart.dualMapR f)) rfl rfl (by simp [spMap]) ob
  obtain ⟨n₁, -⟩ := ObjComp.objMap_comp m₁ r
  obtain ⟨n₂, -⟩ := ObjComp.objMap_comp m₂ r
  exact LevelQuotUnram.unram_of_isAlgClosed hL Xo₂ Q _ _ o' n₁ (LevelQuotUnram.constPt_dualMap f x ▸ n₂)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolFamBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull GlobalTheory.PolBaseChange

theorem polFam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (R' : Type) [CommRing R'] (ρ : R →+* R'), PolFam b Mat κ β v A L act Q → ∃ act' Q', PolFam b Mat κ (ρ.comp β) (fun a => ρ (v a)) ((Over.pullback (spMap ρ)).obj A) (L.pull (pullback.fst A.hom (spMap ρ))) act' Q' := by
  intro o _ g N' J b Mat κ R _ β v A _ L act Q R' _ ρ ⟨hab, hdim, hL, hrig, hsym, hamp, ⟨hhom, htor, hbij⟩, hfib⟩
  have h := isGrpPullback_pullback A (spMap ρ)
  have hL' := LB.isLB_pull hL (pullback.fst A.hom (spMap ρ))
  have hiso := lbIso_refl hL'
  obtain ⟨hab', hamp', -⟩ := pol_pull _ _ _ _ _ _ _ _ hL hL' hab h hiso
  choose pt hpt using fun i => exists_sec h (Q i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst A.hom (spMap ρ) = spMap ρ ≫ (Q i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := hab.comm
  refine ⟨fun j => (Over.pullback (spMap ρ)).map (act j), pt, hab',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hdim, hL', rigidified_pull h hrig,
    sym_pull h hsym, hamp' hamp, ⟨fun j => inferInstance, fun i => pushHom_injective h _ ?_,
      fun K _ _ x y hy => ?_⟩, fun K _ _ x s t ht => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase (spMap ρ))) _ _).symm.trans (by rw [htor, map_one])
  · have key : ∀ c : Ix g N', pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R')) ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ spMap ρ) (by simp) :
          Over.mk (x ≫ spMap ρ) ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ spMap ρ) ≫ (Q i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ N' = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := hbij K (x ≫ spMap ρ) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · obtain ⟨ψ, ⟨k₁, k₄, k₃⟩, k₂⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    rw [spMap_comp] at k₁ k₃
    have hp := h.1
    obtain ⟨F, hF, hw⟩ : ∃ F : t.A.left ⟶ ((Over.pullback (spMap ρ)).obj A).left,
        F ≫ pullback.fst A.hom (spMap ρ) = ψ ∧
        F ≫ ((Over.pullback (spMap ρ)).obj A).hom = t.A.hom ≫ spMap x :=
      ⟨hp.lift ψ (t.A.hom ≫ spMap x) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    subst hF
    have h₄ : ∀ j, ((Over.pullback (spMap ρ)).map (act j)).left ≫ pullback.fst A.hom (spMap ρ) =
        pullback.fst A.hom (spMap ρ) ≫ (act j).left := fun j => pullback.lift_fst _ _ _
    refine ⟨F, ⟨h.cancel k₁ hw, fun j => ?_, fun i => ?_⟩, ?_⟩
    · apply hp.hom_ext
      · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
      · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
    · apply hp.hom_ext
      · rw [Category.assoc, k₃, Category.assoc, Category.assoc, hpt']
      · have a₁ : (t.pt i ^ N').left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt i ^ N')
        have a₂ : (pt i).left ≫ ((Over.pullback (spMap ρ)).obj A).hom = 𝟙 _ := Over.w (pt i)
        rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact LBIso.trans t.isLB (LB.isLB_pull hL _) (LB.isLB_pull hL' _) k₂ (lbIso_pull_comp hiso F).symm

end GlobalTheory.ZM.NearBuild
end
end


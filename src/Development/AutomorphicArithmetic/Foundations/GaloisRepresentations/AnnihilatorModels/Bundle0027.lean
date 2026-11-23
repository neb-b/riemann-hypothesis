module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecSurj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.secSurj_of :
    ConstSub → OMod → QuotObj → ObjTri → PullKer → SecSurj := by
  intro hCS hOM hQO hOT hPK
  intro p _ D O _ _ _ _ f b N r w _ hstd M j hj T K _ _ hp x G hGk hGs hGc
  obtain ⟨o₁, ⟨m⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D O b N M.X (Sp K) M.s x M.univ
  have hcm : ∀ {X Y Z : Over M.X} [MonObj Z] (e : X ⟶ Y) (u v : Y ⟶ Z), e ≫ (u * v) = (e ≫ u) * (e ≫ v) := by
    intro X Y Z _ e u v
    rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, CartesianMonoidalCategory.comp_lift]
  let eI : Over.mk x ≅ (Over.map x).obj (𝟙_ (Over (Sp K))) := Over.isoMk (Iso.refl _) (by simp)
  let Φ : (𝟙_ (Over (Sp K)) ⟶ o₁.A) →* (Over.mk x ⟶ M.univ.A) :=
    { toFun := fun u => eI.hom ≫ m.ptEquiv _ u
      map_one' := by rw [map_one]; simp [Hom.one_def]
      map_mul' := fun a c => by rw [map_mul]; exact hcm _ _ _ }
  have hΦl : ∀ u, (Φ u).left = u.left ≫ m.φ := fun u => by
    simp [Φ, eI, GlobalTheory.UPel.HT.ObjMap.ptEquiv_left]
  have hΦi : Function.Injective Φ := fun a c h => by
    have h2 : m.ptEquiv _ a = m.ptEquiv _ c := by
      simpa [Φ] using congrArg (fun t => eI.inv ≫ t) h
    exact (m.ptEquiv _).injective h2
  have hΦs : Function.Surjective Φ := fun g => ⟨(m.ptEquiv _).symm (eI.inv ≫ g), by simp [Φ]⟩
  have hPK1 := hPK p D O b N M.X (Sp K) M.s (x ≫ M.s) x M.univ M.univ o₁ o₁ m m (𝟙 _) (𝟙 _) (by simp)
  have hkill : ∀ u I, KilledBy o₁ I u ↔ KilledBy M.univ I (Φ u) := fun u I =>
    ((hPK1.1 (𝟙_ (Over (Sp K))) (Over.mk x) rfl u (Φ u) (by simp [hΦl])).2.2 I)
  have hpw : (p : 𝓞 D.F) ∈ w := hstd.ule (GlobalTheory.UPel.HT.ES.p_mem_uIdeal D r)
  have hGO : ∀ g ∈ G, ∀ a : D.O, g ≫ M.univ.act.act a ∈ G := by
    intro g hg a
    obtain ⟨c, y', rfl⟩ := hOM p D hstd.m1 a
    have h1 : g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O (p : 𝓞 D.F)) = 1 := hGk g hg _ hpw
    haveI := M.univ.act.hom y'
    rw [GlobalTheory.UPel.HT.OActN.add, hcm, Algebra.commutes, GlobalTheory.UPel.HT.OActN.mul, ← Category.assoc, h1]
    simp only [Hom.one_def, Category.assoc, IsMonHom.one_hom]
    rw [← Hom.one_def, _root_.mul_one]
    exact hGs g hg c
  have hcard : Nat.card (G.comap Φ) = Nat.card G :=
    Nat.card_congr ((Subgroup.equivMapOfInjective (G.comap Φ) Φ hΦi).toEquiv.trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective hΦs G)).toEquiv)
  have hne : Nat.card G ≠ 0 := by
    rw [hGc, hstd.norm]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero)
  have hfin : Finite (G.comap Φ) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  haveI := o₁.ab
  haveI := IsAbelianScheme.proper (A := o₁.A)
  obtain ⟨G', _, i, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ := hCS K o₁.A inferInstance (G.comap Φ) hfin
  have hΦact : ∀ u a, Φ (u ≫ o₁.act.act a) = Φ u ≫ M.univ.act.act a := fun u a =>
    Over.OverMorphism.ext (by rw [hΦl, Over.comp_left, Over.comp_left, hΦl, Category.assoc, Category.assoc, m.act])
  have hks : ∀ (T' : Over (Sp K)) (z : T' ⟶ o₁.A), GlobalTheory.IwLevel.InSub i z → KilledBy o₁ w z := by
    rintro T' z ⟨y0, rfl⟩ a ha
    have h7 : i ≫ o₁.act.act (algebraMap _ _ a) = 1 :=
      hi7 _ (fun u hu => ((hkill u w).2 (hGk _ hu)) a ha)
    rw [Category.assoc, h7]
    simp [Hom.one_def]
  have hstab : ∀ a : D.O, ∃ g, g ≫ i = i ≫ o₁.act.act a := fun a =>
    hi8 _ (fun u hu => by
      rw [Subgroup.mem_comap, hΦact]
      exact hGO _ hu a)
  have hisog : GlobalTheory.IwLevel.IsIsogDeg (toUnit G') (Ideal.absNorm w ^ j) := by
    rw [← hGc, ← hcard]; exact hi5
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h := hstd.card
      rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at h
      exact (not_subsingleton _) h.1
    · exact h0
  have hu : IsUnit (p : Γ(Sp K, ⊤)) := by
    have h0 : IsUnit (p : K) := hp.isUnit
    simpa using h0.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨o', ψ, hψ1, hψ2, hψ3⟩ := hQO p D O b N hstd.three hstd.cop hstd.m1 r w j (p ^ (f * j)) inferInstance
    hstd.ule hj ⟨f * j, rfl, fun h => Nat.mul_pos hf0 h⟩ (Sp K) (x ≫ M.s) hu o₁ G' i hi1 hi2 hi3 hi4 hks
    hstab hisog
  obtain ⟨y, ⟨hy, m₀, m₁, hsq⟩, -⟩ := T.univ (Sp K) x o₁ o' m ψ hu hψ1 hψ2
  refine ⟨y, hy, fun g hg => ?_⟩
  obtain ⟨u, rfl⟩ := hΦs g
  have key : m₀.φ ≫ T.ms.φ = m.φ := by
    obtain ⟨m₂, hm₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ T.ms
    have hcast : ∀ (f₁ f₂ : Sp K ⟶ M.X) (h : f₁ = f₂) (mm : GlobalTheory.UPel.HT.ObjMap o₁ M.univ f₂),
        ∃ mm' : GlobalTheory.UPel.HT.ObjMap o₁ M.univ f₁, mm'.φ = mm.φ := by
      rintro f₁ f₂ rfl mm
      exact ⟨mm, rfl⟩
    obtain ⟨m', hm'⟩ := hcast _ _ hy m
    rw [← hm', ← hm₂]
    exact (hOT p D O b N hstd.three hstd.cop _ _ _ _ _ _ o₁ M.univ M.univ _ (𝟙 _)).1 m₂ m'
  have h1 : Φ u ∈ G ↔ u ≫ ψ = 1 := by
    rw [← Subgroup.mem_comap, ← hi6, ← hψ3]
    exact ⟨fun h => h.1, fun h => ⟨h, 1, by
      rw [pow_one]
      intro a ha
      exact ((hkill u w).2 hg) a (hstd.ule ha)⟩⟩
  have hPK2 := hPK p D O b N T.Y (Sp K) (T.s ≫ M.s) (x ≫ M.s) y T.o T.o' o₁ o' m₀ m₁ T.ψ ψ hsq
  let eY : Over.mk y ≅ (Over.map y).obj (𝟙_ (Over (Sp K))) := Over.isoMk (Iso.refl _) (by simp)
  let a₀ : Over.mk y ⟶ T.o.A := eY.hom ≫ m₀.ptEquiv _ u
  have hl0 : a₀.left = u.left ≫ m₀.φ := by
    simp [a₀, eY, GlobalTheory.UPel.HT.ObjMap.ptEquiv_left]
  constructor
  · intro hK
    have ha0 : a₀ ≫ T.ψ = 1 := hK a₀ (by rw [hl0, Category.assoc, key, hΦl])
    rw [h1]
    exact ((hPK2.1 _ _ rfl u a₀ (by rw [eqToHom_refl, Category.id_comp, hl0])).1).2 ha0
  · intro hG a' ha'
    rw [h1] at hG
    let u' := (m₀.ptEquiv _).symm (eY.inv ≫ a')
    have hu'l : u'.left ≫ m₀.φ = a'.left := by
      rw [← GlobalTheory.UPel.HT.ObjMap.ptEquiv_left]
      simp [u', eY]
    have huu : u' = u := hΦi (Over.OverMorphism.ext (by
      rw [hΦl, hΦl, ← key, ← Category.assoc, hu'l, ha', hΦl, key]))
    exact ((hPK2.1 _ _ rfl u a' (by rw [eqToHom_refl, Category.id_comp, ← huu, hu'l])).1).1 hG
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isUnit_natCast_of {X Y : Scheme.{0}} (g : X ⟶ Y) {n : ℕ} (h : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  have := h.map g.appTop.hom
  rwa [map_natCast] at this

private theorem exists_id {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hN : 3 ≤ N) (hNp : N.Coprime p) {S S₃ : Scheme.{0}} {s : S ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o : Obj b N s} {o₃ : Obj b N s₃} {g : S ⟶ S₃} (m : ObjMap o o₃ g) :
    ∃ i : ObjMap o o (𝟙 S), i.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := (hT p D R b N hN hNp _ _ _ _ _ _ o o o₃ (𝟙 S) g).2 g (Category.id_comp g) m m
  refine ⟨i, m.cart.1.hom_ext ?_ ?_⟩
  · rw [hi, Category.id_comp]
  · rw [i.cart.1.w, Category.comp_id, Category.id_comp]

private theorem et_of {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (hT : ObjTri) (hI : PullIsog) (hK : PullKer) (hN : 3 ≤ N) (hNp : N.Coprime p)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}
    {Y : Scheme.{0}} {s : Y ⟶ M.X} {o o' : Obj b N (s ≫ M.s)} (ms : ObjMap o M.univ s) {ψ : o.A ⟶ o'.A}
    (iso : IsPIsog c o o' ψ) (tj : IsTj r w j o o' ψ) (hY : Univ r w j c M s o o' ψ)
    {Y₀ : Scheme.{0}} {s₀ : Y₀ ⟶ M.X} (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme)
    (hgs : gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀) (egs : Etale gs)
    {o₀ o₀' : Obj b N (s₀ ≫ M.s)} (ms₀ : ObjMap o₀ M.univ s₀) {ψ₀ : o₀.A ⟶ o₀'.A}
    (iso₀ : IsPIsog c o₀ o₀' ψ₀) (tj₀ : IsTj r w j o₀ o₀' ψ₀) (hY₀ : Univ r w j c M s₀ o₀ o₀' ψ₀) :
    Etale (s ∣_ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
  have hpU : IsUnit ((p : ℕ) : Γ((M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme, ⊤)) := by
    have h0 := GlobalTheory.EtC.PairDich.isUnit_ι_appTop (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) ((p : ℕ) : Γ(M.X, ⊤)) le_rfl
    rwa [map_natCast] at h0
  have hp₀ : IsUnit ((p : ℕ) : Γ(Y₀, ⊤)) := isUnit_natCast_of gs hpU
  have hpV : IsUnit ((p : ℕ) : Γ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme, ⊤)) :=
    isUnit_natCast_of (s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))) hpU
  have hPB := isPullback_morphismRestrict s (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))
  obtain ⟨oV, ⟨mV⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme M.s
    ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) M.univ
  obtain ⟨mVo, -⟩ := (hT p D R b N hN hNp _ Y M.X _ (s ≫ M.s) M.s oV o M.univ
    (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι s).2 _ rfl mV ms
  obtain ⟨oV', mV', ψV, isoV, sqV⟩ := hI p D R b N Y (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme
    (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι (Category.assoc _ _ _).symm c o o' ψ iso oV mVo
  have tjV := (hK p D R b N Y _ (s ≫ M.s) _ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι
    o o' oV oV' mVo mV' ψ ψV sqV).2 r w j tj
  obtain ⟨y₀, ⟨hy₀, m₀y, m₁y, hsq₀⟩, -⟩ := hY Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀
  obtain ⟨v, ⟨hv, m₀v, m₁v, hsqv⟩, -⟩ :=
    hY₀ _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV
  have hvy : v ≫ y₀ = (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι := by
    apply (hY _ ((s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι ≫ s) oV oV' mV ψV hpV isoV tjV).unique
    · refine ⟨by rw [Category.assoc, hy₀, hv], ?_⟩
      obtain ⟨a, ha⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀v m₀y
      obtain ⟨a', ha'⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁v m₁y
      refine ⟨a, a', ?_⟩
      rw [ha, ha', Category.assoc m₀v.φ m₀y.φ, hsq₀, ← Category.assoc m₀v.φ, hsqv,
        Category.assoc (Over.Hom.left ψV) m₁v.φ m₁y.φ]
    · exact ⟨rfl, mVo, mV', sqV⟩
  let u : Y₀ ⟶ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).toScheme := hPB.lift gs y₀ (by rw [hgs, hy₀])
  have hu₁ : u ≫ s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) = gs := hPB.lift_fst _ _ _
  have hu₂ : u ≫ (s ⁻¹ᵁ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)))).ι = y₀ := hPB.lift_snd _ _ _
  have hvg : v ≫ gs = s ∣_ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) := by
    rw [← cancel_mono (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι, Category.assoc, hgs, hv, morphismRestrict_ι]
  have hvu : v ≫ u = 𝟙 _ := by
    apply hPB.hom_ext
    · rw [Category.assoc, hu₁, hvg, Category.id_comp]
    · rw [Category.assoc, hu₂, hvy, Category.id_comp]
  have huv : u ≫ v = 𝟙 Y₀ := by
    apply (hY₀ Y₀ s₀ o₀ o₀' ms₀ ψ₀ hp₀ iso₀ tj₀).unique
    · refine ⟨by rw [Category.assoc, hv, ← Category.assoc, hu₂, hy₀], ?_⟩
      have hc : (u ≫ v) ≫ y₀ = y₀ := by rw [Category.assoc, hvy, hu₂]
      obtain ⟨a, ha⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀ o₀ o (u ≫ v) y₀).2 y₀ hc m₀y m₀y
      obtain ⟨a', ha'⟩ := (hT p D R b N hN hNp Y₀ Y₀ Y _ _ _ o₀' o₀' o' (u ≫ v) y₀).2 y₀ hc m₁y m₁y
      refine ⟨a, a', ?_⟩
      apply m₁y.cart.1.hom_ext
      · rw [Category.assoc a.φ, ← hsq₀, ← Category.assoc a.φ, ha, hsq₀, Category.assoc (Over.Hom.left ψ₀) a'.φ, ha']
      · have e1 := a.cart.1.w
        have e2 := a'.cart.1.w
        calc (a.φ ≫ Over.Hom.left ψ₀) ≫ o₀'.A.hom = a.φ ≫ o₀.A.hom := by rw [Category.assoc a.φ, Over.w]
          _ = o₀.A.hom ≫ (u ≫ v) := e1
          _ = (Over.Hom.left ψ₀ ≫ o₀'.A.hom) ≫ (u ≫ v) := by rw [Over.w]
          _ = (Over.Hom.left ψ₀ ≫ a'.φ) ≫ o₀'.A.hom := by
            rw [Category.assoc (Over.Hom.left ψ₀) o₀'.A.hom, ← e2, Category.assoc (Over.Hom.left ψ₀) a'.φ]
    · refine ⟨Category.id_comp _, ?_⟩
      obtain ⟨i, hi⟩ := exists_id hT hN hNp ms₀
      obtain ⟨i', hi'⟩ := exists_id hT hN hNp m₁y
      exact ⟨i, i', by rw [hi, hi', Category.id_comp, Category.comp_id]⟩
  haveI : IsIso v := ⟨⟨u, hvu, huv⟩⟩
  rw [← hvg]
  infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.tjExF_of :
    EsNorm → EsGen → ObjTri → PullIsog → PullKer → TjExF := by
  intro hE hG hT hI hK p _ D O _ _ _ _ f b N r w _ hS M j hj
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := hS.norm
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at h1
      exact absurd h1 (Ideal.IsMaximal.ne_top inferInstance)
    · exact h
  have hc : ∃ e : ℕ, p ^ (f * j) = p ^ e ∧ (0 < j → 0 < e) :=
    ⟨f * j, rfl, fun h => Nat.mul_pos hf h⟩
  obtain ⟨Y, s, t, o, o', ms, mt, ψ, st, fin, -, -, flat, iso, tj, univ⟩ :=
    hE p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  obtain ⟨Y₀, s₀, t₀, gs, gt, o₀, o₀', ms₀, mt₀, ψ₀, -, hgs, -, -, egs, -, -, iso₀, tj₀, univ₀⟩ :=
    hG p D O b N hS.three hS.cop hS.pmem r w j (p ^ (f * j)) inferInstance hS.ule hj hc hS.m1 M
  exact ⟨⟨Y, s, t, st, o, o', ms, mt, ψ, fin,
    et_of hT hI hK hS.three hS.cop ms iso tj univ gs hgs egs ms₀ iso₀ tj₀ univ₀, iso, tj, univ⟩, flat⟩
end


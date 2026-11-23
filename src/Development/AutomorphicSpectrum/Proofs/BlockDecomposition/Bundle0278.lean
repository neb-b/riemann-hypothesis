module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0233
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0159
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0273

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueChernClassNilpotentBase
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

theorem mapH_bijective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{1} R} {M : Cx.{1} R'}
    (φ : Cx.Hom K M σ) (h : ∀ n, Function.Bijective (φ.f n)) (n : ℕ) : Function.Bijective (φ.mapH n) := by
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (φ.mapH n)).2 fun x hx => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ.f n z.1 ∈ M.B n := (Submodule.Quotient.mk_eq_zero ((M.B n).submoduleOf (M.Z n)) (x := φ.mapZ n z)).1 hx
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change z.1 ∈ K.B n
    cases n with
    | zero =>
      have h2 : φ.f 0 z.1 = 0 := h1
      have h3 : z.1 = 0 := (h 0).1 (h2.trans (map_zero _).symm)
      rw [h3]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy⟩ := h1
      obtain ⟨y', rfl⟩ := (h n).2 y
      refine ⟨y', (h (n + 1)).1 ?_⟩
      rw [← φ.comm, hy]
  · intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, hx⟩ := (h n).2 w.1
    have h0 : K.d n x = 0 := (h (n + 1)).1 (by
      rw [← φ.comm, hx, map_zero]
      exact w.2)
    exact ⟨Submodule.Quotient.mk ⟨x, h0⟩, congrArg _ (Subtype.ext hx)⟩

section Gen

variable {b : Base} {L : b.Fun} {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def toO (Q : ObjectProperty (Thick L)) : CH.Mor (Q.ι ⋙ B.OM L c) (CH.modF (sP Q).A) c where
  G := 𝟭 _
  τ T := { toFun := fun x => x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  nat _ _ := rfl

theorem toO_bij (Q : ObjectProperty (Thick L)) (n : ℕ) : Function.Bijective ((toO c Q).pull n) :=
  mapH_bijective _ (fun _ => Function.bijective_id) n

def sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) : CH.Mor (P.ι ⋙ B.OM L c) (Q.ι ⋙ B.OM L c) (RingHom.id Λ) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem sub_square {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (toO c Q).pull j ((sub c h).pull j x) = (incl h).o.pull j ((toO c P).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem sub_bij {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (hb : Function.Bijective ((incl h).o.pull j)) :
    Function.Bijective ((sub c h).pull j) := by
  have e : (toO c Q).pull j ∘ (sub c h).pull j = (incl h).o.pull j ∘ (toO c P).pull j :=
    funext (sub_square c h j)
  refine (Function.Bijective.of_comp_iff' (toO_bij c Q j) _).1 ?_
  rw [e]
  exact hb.comp (toO_bij c P j)

theorem sub_sub {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h' : S ≤ Q) (j : ℕ) (x : CH.H (P.ι ⋙ B.OM L c) j) :
    (sub c h').pull j ((sub c h).pull j x) = (sub c (h'.trans h)).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_sub {P Q : ObjectProperty (Thick L)} (h : Q ≤ P) (j : ℕ) (x : CH.H (B.OM L c) j) :
    (sub c h).pull j ((CH.Mor.restrict (B.OM L c) P.ι).pull j x) = (CH.Mor.restrict (B.OM L c) Q.ι).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem res_all (P : ObjectProperty (Thick L)) (hP : ∀ T, P T) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) P.ι).pull j) := by
  refine mapH_bijective _ (fun n => ⟨fun f g e => ?_, fun g => ?_⟩) j
  · funext t
    exact congrFun e (P.lift t fun i => hP _)
  · exact ⟨fun t => g (P.lift t fun i => hP _), rfl⟩

theorem bij_three {P Q S : ObjectProperty (Thick L)} (h : Q ≤ P) (h1 : S ≤ Q) (h2 : S ≤ P) (j : ℕ)
    (b1 : Function.Bijective ((incl h1).o.pull j)) (b2 : Function.Bijective ((incl h2).o.pull j)) (hP : ∀ T, P T) :
    Function.Bijective ((CH.Mor.restrict (B.OM L c) Q.ι).pull j) := by
  have s1 := sub_bij c h1 j b1
  have s2 := sub_bij c h2 j b2
  have s3 : Function.Bijective ((sub c h).pull j) := by
    have e : (sub c h1).pull j ∘ (sub c h).pull j = (sub c h2).pull j := funext (sub_sub c h h1 j)
    refine (Function.Bijective.of_comp_iff' s1 _).1 ?_
    rw [e]
    exact s2
  have e : (sub c h).pull j ∘ (CH.Mor.restrict (B.OM L c) P.ι).pull j =
      (CH.Mor.restrict (B.OM L c) Q.ι).pull j := funext (res_sub c h j)
  rw [← e]
  exact s3.comp (res_all c _ hP j)

end Gen

end GlobalTheory.CompanionTheory.CrystallineChernClass

namespace GlobalTheory.CompanionTheory.CrystallineChernClass

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

theorem exu_core (D : E.LineData X) (Q : ObjectProperty (Thick ((B.schFn q).cr b ht κ)))
    (hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T)
    {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (N : ℕ)
    (hbij : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2))
    (hN : ∀ (T : Thick ((B.schFn q).cr b ht κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0) :
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := b) (ht := ht) (κ := κ) D c N x := by
  obtain ⟨Λ₀⟩ := GlobalTheory.CompanionTheory.CLiftEx.nonempty_cLift Q.ι D (fun T => (hQ _).1 T.property)
  have hz₀ := (_root_.GlobalTheory.CompanionTheory.CocCls.coc_cls Q.ι D c N (fun T k hk x _ => by
    change ((k.factorial : ℕ) : (T.obj).B) * _ = 0
    rw [hN _ k hk, zero_mul])).1 Λ₀
  obtain ⟨x, hx⟩ := hbij.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G Λ₁
    have hG : ∀ T, Q (G.obj T) := fun T => (hQ _).2 ⟨Λ₁.p T, Λ₁.hp T⟩
    have hcl := _root_.GlobalTheory.CompanionTheory.CocCls.coc_cls G D c N (fun T k hk x _ => by rw [hN _ k hk, zero_mul])
    let Λ' : B.CLift G D := precomp Λ₀ (Q.lift G hG)
    refine ⟨hcl.1 Λ₁, ?_⟩
    rw [hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')]
    have e1 : (CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) G).pull 2 x =
        (CH.Mor.restrict (Q.ι ⋙ B.OM ((B.schFn q).cr b ht κ) c) (Q.lift G hG)).pull 2
          ((CH.Mor.restrict (B.OM ((B.schFn q).cr b ht κ) c) Q.ι).pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hbij.1
    obtain ⟨h1, h2⟩ := hy _ Q.ι Λ₀
    rw [hx, ← h2]

end Core

section Main

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def Lifts (D : E.LineData X) : ObjectProperty (Thick (nlFun γ p X q κ)) :=
  fun T => ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T

theorem st_le_lifts (D : E.LineData X) : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ Lifts D := by
  rintro T ⟨-, V, ⟨σ, hσ⟩, hV⟩
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem inU_top (T : Thick (nlFun γ p X q κ)) : InU ⊤ T := fun _ _ => trivial

theorem lifts_map (D : E.LineData X) {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : Lifts D T) : Lifts D T' := by
  obtain ⟨a, ha⟩ := h
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ a, ?_⟩
  rw [Category.assoc, ha]
  exact congrArg (fun y => y.1.2) φ.pt

theorem res_bij (hp : p ≠ 0) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ] (c : Λ →+* R) (j : ℕ) :
    Function.Bijective ((CH.Mor.restrict (B.OM (nlFun γ p X q κ) c) (Lifts D).ι).pull j) := by
  have hU : Used (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) := Or.inr ⟨hp, Or.inl rfl⟩
  have h1 : St ⊤ (𝒱D D) ≤ Lifts (γ := γ) (p := p) (q := q) (κ := κ) D := st_le_lifts D
  have h1' : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {sSup (𝒱D D)} := fun T _ =>
  ⟨trivial, _, rfl, by rw [hD]; exact inU_top T⟩
  have b1 := (_root_.GlobalTheory.CompanionTheory.ZarCosieve.main ⊤ hU (𝒱D D) (Lifts D) h1 h1' (fun T T' φ h _ => lifts_map D φ h) j).2.2
  have h2 : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (𝒱D D) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have b2 := (_root_.GlobalTheory.CompanionTheory.NlZar.zariski_descent ⊤ hU (𝒱D D) {⊤} h2 (by rintro W rfl; rw [hD]) j).2.2
  have h3 : Lifts (γ := γ) (p := p) (q := q) (κ := κ) D ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, inU_top T⟩
  have hall : ∀ T, St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ {⊤} T := fun T => ⟨trivial, ⊤, rfl, inU_top T⟩
  exact bij_three (b := nlBase R I γ p) (L := nlFun γ p X q κ) c h3 h1 h2 j b1 b2 hall

end Main

theorem existsUnique_crystalline_chern_class : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) (D : E.LineData X) (hD : sSup (𝒱D D) = ⊤) {Λ : Type} [CommRing Λ]
    (c : Λ →+* R) (N : ℕ), (N.factorial : R) = 0 →
    ∃! x, B.IsFirstChernClassOfLineBundle (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D c N x := by
  intro O R _ _ I γ p hp X q κ D hD Λ _ c N hN
  have hf : ∀ (T : Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) (k : ℕ), N ≤ k → (k.factorial : T.B) = 0 := fun T k hk => by
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hk
    have h0 : (k.factorial : R) = 0 := by rw [hm, Nat.cast_mul, hN, zero_mul]
    have := congrArg T.i h0
    rwa [map_natCast, map_zero] at this
  have hb := res_bij (γ := γ) (q := q) (κ := κ) hp D hD c 2
  let Q : ObjectProperty (Thick ((B.schFn q).cr (nlBase R I γ p) rfl κ)) := Lifts (γ := γ) (p := p) (q := q) (κ := κ) D
  have hQ : ∀ T, Q T ↔ ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = B.thPt T := fun T => Iff.rfl
  have hb' : Function.Bijective ((CH.Mor.restrict (B.OM ((B.schFn q).cr (nlBase R I γ p) rfl κ) c) Q.ι).pull 2) := hb
  exact exu_core (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) D Q hQ c N hb' hf

end GlobalTheory.CompanionTheory.CrystallineChernClass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentMemFinset
section
open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Latexp

open GroundTheory.Automorphic.Reduction in
theorem detModule_tor_one (K : Type) [Field K] [NumberField K] (n : ℕ) :
    (detModule K n (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) : ℝ)
      = Real.exp ((n : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  unfold PositivityTheory.Rg.Rs.An.tor
  rw [CuspidalSpectrum.detModule_diagUnits_posIdele]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← Real.exp_nat_mul]
  simp

open GroundTheory.Automorphic.Reduction in
theorem detModule_lhs (K : Type) [Field K] [NumberField K] (n : ℕ) (γ₀ : GL (Fin n) K) (m : ℤ) :
    (detModule K n (AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m) : ℝ)
      = Real.exp ((m : ℝ) * ((n : ℝ) * (Module.finrank ℚ K : ℝ))) := by
  have h1 : detModule K n (AdelicGLn.diagonal K n γ₀) = 1 :=
    mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨γ₀, rfl⟩)
  rw [map_mul, h1, one_mul, map_zpow]
  have hv : ∀ (s : {r : ℝ // 0 < r}) (k : ℤ), ((s ^ k : {r : ℝ // 0 < r}) : ℝ) = (s : ℝ) ^ k := by
    intro s k
    have hinv : ∀ u : {r : ℝ // 0 < r}, ((u⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ)⁻¹ := by
      intro u
      have h := congrArg Subtype.val (mul_inv_cancel u)
      rw [Positive.val_mul, Positive.val_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hpow : ∀ (u : {r : ℝ // 0 < r}) (j : ℕ), ((u ^ j : {r : ℝ // 0 < r}) : ℝ) = (u : ℝ) ^ j := by
      intro u j
      induction j with
      | zero => simp
      | succ j ih => rw [pow_succ, pow_succ, Positive.val_mul, ih]
    cases k with
    | ofNat j => simp only [Int.ofNat_eq_natCast, zpow_natCast, hpow]
    | negSucc j => rw [zpow_negSucc, zpow_negSucc, hinv, hpow]
  rw [hv, detModule_tor_one, ← Real.rpow_intCast, ← Real.exp_mul, mul_comm]

open GroundTheory.Automorphic.Reduction in
theorem detModule_rhs (K : Type) [Field K] [NumberField K] (n r : ℕ) (X Y : UPos n r → 𝔸[K])
    (a q : AdelicGLn.AdelicGL K n) :
    detModule K n (unipGL X * a * q * a⁻¹ * (unipGL Y)⁻¹) = detModule K n q := by
  have h1 : detModule K n (unipGL X) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL X)
  have h2 : detModule K n (unipGL Y) = 1 :=
    mem_normOneGL_iff_detModule.1 (CuspidalSpectrum.unipGL_mem_normOneGL Y)
  simp only [map_mul, map_inv, h1, h2, inv_one, one_mul, mul_one]
  rw [mul_comm (detModule K n a), mul_assoc, mul_inv_cancel, mul_one]

end GlobalTheory.CompanionTheory.Latexp

namespace GlobalTheory.CompanionTheory.Latexp

open GroundTheory.Automorphic.Reduction in
theorem exponent_mem_finset : ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < n → ∀ (Q : Set (AdelicGLn.AdelicGL K n)), IsCompact Q → ∃ M : Finset ℤ, ∀ (t : ℝ) (X Y : UPos n r → 𝔸[K]), ∀ q ∈ Q, ∀ (γ₀ : GL (Fin n) K) (m : ℤ), AdelicGLn.diagonal K n γ₀ * (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) ^ m = unipGL X * PositivityTheory.Rg.Rs.An.aR K n r t * q * (PositivityTheory.Rg.Rs.An.aR K n r t)⁻¹ * (unipGL Y)⁻¹ → m ∈ M := by
  intro K _ _ n r hn Q hQ
  have hdc : Continuous fun g : AdelicGLn.AdelicGL K n => (detModule K n g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  obtain ⟨a, b, ha, -, hab⟩ := Reduction.exists_pos_bounds hQ hdc (fun g _ => (detModule K n g).2)
  have hN : 0 < (n : ℝ) * (Module.finrank ℚ K : ℝ) :=
    mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 Module.finrank_pos)
  set N : ℝ := (n : ℝ) * (Module.finrank ℚ K : ℝ) with hNdef
  refine ⟨Finset.Icc ⌊Real.log a / N⌋ ⌈Real.log b / N⌉, ?_⟩
  intro t X Y q hq γ₀ m h
  have h1 := congrArg (fun g => (detModule K n g : ℝ)) h
  beta_reduce at h1
  rw [detModule_lhs, detModule_rhs] at h1
  obtain ⟨h2, h3⟩ := hab q hq
  rw [← h1] at h2 h3
  have h4 : Real.log a ≤ (m : ℝ) * N := (Real.log_le_iff_le_exp ha).2 h2
  have h5 : (m : ℝ) * N ≤ Real.log b := by
    have hb : 0 < b := lt_of_lt_of_le (Real.exp_pos _) h3
    exact (Real.le_log_iff_exp_le hb).2 h3
  rw [Finset.mem_Icc]
  constructor
  · have : Real.log a / N ≤ (m : ℝ) := (div_le_iff₀ hN).2 h4
    exact Int.cast_le.1 ((Int.floor_le _).trans this)
  · have : (m : ℝ) ≤ Real.log b / N := (le_div_iff₀ hN).2 h5
    exact Int.cast_le.1 (this.trans (Int.le_ceil _))
end GlobalTheory.CompanionTheory.Latexp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotients
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.JHMult
open PositivityTheory.Rg.BcN.F2 (FinSubq)

namespace GlobalTheory.CompanionTheory.RepFinSubq

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_series {ρ : Representation F G V} (h : HasFiniteLength ρ) :
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧
      ∀ t : Fin N, S t.castSucc ⋖ S t.succ := by
  obtain ⟨s, h0, h1⟩ := isFiniteLength_iff_exists_compositionSeries.1 h
  let e := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm
  refine ⟨s.length, fun i => e (s i), ?_, ?_, ?_, fun t => ?_⟩
  · exact e.monotone.comp s.strictMono.monotone
  · show e s.head = ⊥
    rw [h0, map_bot]
  · show e s.last = ⊤
    rw [h1, map_top]
  · exact (apply_covBy_apply_iff e).2 (s.step t)

theorem isSubquotient_subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    IsSubquotient (subQuot S T) ρ :=
  ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩

theorem exists_factor_equiv {ρ : Representation F G V} {N : ℕ} {S : Fin (N + 1) → Subrepresentation ρ}
    (hS : Monotone S) (h0 : S 0 = ⊥) (h1 : S (Fin.last N) = ⊤) (hc : ∀ t : Fin N, S t.castSucc ⋖ S t.succ)
    {τ : Representation F G W} (hτ : τ.IsIrreducible) (hq : IsSubquotient τ ρ) :
    ∃ t : Fin N, Nonempty (τ.Equiv (subQuot (S t.succ) (S t.castSucc))) := by
  have hne : jhMult τ ρ ≠ 0 := jhMult_ne_zero_iff.2 hq
  rw [jhMult_filtration hτ S hS h0 h1] at hne
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨e⟩ := (jhMult_ne_zero_iff.1 ht).nonempty_equiv hτ (isIrreducible_subQuot (hc t))
  exact ⟨t, ⟨e.symm⟩⟩

theorem finSubq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  intro F _ _ _ _ ι _ _ U _ _ ρ hρ hfl
  obtain ⟨N, S, hS, h0, h1, hc⟩ := exists_series hfl
  refine ⟨Fin N, inferInstance, fun t => _, fun _ => inferInstance, fun _ => inferInstance,
    fun t => subQuot (S t.succ) (S t.castSucc), fun t => ?_, fun W' _ _ τ' hτ hq => ?_⟩
  · exact ⟨(isSubquotient_subQuot _ _).isSmooth hρ, isIrreducible_subQuot (hc t), isSubquotient_subQuot _ _⟩
  · exact exists_factor_equiv hS h0 h1 hc hτ hq

end GlobalTheory.CompanionTheory.RepFinSubq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHc

theorem subsingleton_Bk_zero (l : ℕ) [Fact l.Prime] : Subsingleton (Lat.Bk l 0) := by
  refine Ideal.Quotient.subsingleton_iff.2 ?_
  rw [pow_zero, Ideal.span_singleton_one]

theorem hc_k : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ),
    Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  intro l _ M k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x _ n
    haveI := subsingleton_Bk_zero l
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)

end GlobalTheory.CompanionTheory.LatCHc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsGenerate
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_smul_top_of_redL {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V') (hV : IsAffineOpen V)
    (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (hx : redL I Y β hβ L w hL e V V' h.ge x ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V'))) :
    x ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) := by
  obtain ⟨hsurj, hker⟩ := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_surjective_ker R I Y β hβ L w hL e V V' h hV
  have hmap : Submodule.map (redL I Y β hβ L w hL e V V' h.ge)
      (I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V))) =
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V')) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
  rw [← hmap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hk : x - z ∈ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  rw [hker] at hk
  have hk' : x - z ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero e)) hk
  simpa using Submodule.add_mem _ hk' hz

theorem map_mul_sub_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (x y : A) (z : B) :
    ρ (x * y) - ρ x * z = (ρ y - z) * ρ x := by
  rw [map_mul]; ring

theorem map_mem_smul_top {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (φ : M →ₗ[R] M') {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : φ x ∈ I • (⊤ : Submodule R M') := by
  have h := Submodule.mem_map_of_mem (f := φ) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem resT_mulT_sub_mem : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu j e t S S' h a hS
  have hS' : S'.Nonempty := hS.mono h

  have key : ∀ e : ℕ, SecOnR.restrict (toR I Y e) (pw (N e) (d : ℤ)) (hDm e S S' h)
        (SecOnR.of _ _ _ (sh e j S)) - SecOnR.of (toR I Y e) _ _ (sh e j S') ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (pw (N e) (d : ℤ)) (D e S'))) := by
    intro e
    induction e with
    | zero =>
      have : SecOnR.restrict (toR I Y 0) (pw (N 0) (d : ℤ)) (hDm 0 S S' h)
          (SecOnR.of _ _ _ (sh 0 j S)) - SecOnR.of (toR I Y 0) _ _ (sh 0 j S') = 0 := by
        rw [hsh0 j S hS, hsh0 j S' hS', sub_eq_zero]
        exact GlobalTheory.LB.map_ofSec (s j) (hDm 0 S S' h)
      rw [this]
      exact Submodule.zero_mem _
    | succ e ih =>
      refine mem_smul_top_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S')
        (D e S') (hDβ e S') (hDa (e + 1) S' hS') _ ?_
      rw [map_sub]
      have h1 := _root_.GlobalTheory.CompanionTheory.FormalAlg.Lift.redL_restrict R I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
        (D (e + 1) S') (D e S) (D e S') (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h)
        (hDm e S S' h) (SecOnR.of _ _ _ (sh (e + 1) j S))
      have h2 := hshp e j S hS
      have h3 := hshp e j S' hS'
      rw [h1]
      erw [h2, h3]
      exact ih
  have hmem := map_mem_smul_top I
    (mulRight (toR I Y e) (show (d : ℤ) + (d : ℤ) * t = (d : ℤ) * (t + 1) by ring)
      ((SecOnR.of _ _ _).symm (resT I Y N D (d : ℤ) hDm e t h a))) (key e)
  convert hmem using 1
  refine SecOnR.ext fun (i : (N e).ι) => ?_
  exact map_mul_sub_mul (rs (Y e).left (inf_le_inf_right ((N e).U i) (hDm e S S' h)))
    (SecOnR.coord a i) (GlobalTheory.LB.coord (sh e j S) i) (GlobalTheory.LB.coord (sh e j S') i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end


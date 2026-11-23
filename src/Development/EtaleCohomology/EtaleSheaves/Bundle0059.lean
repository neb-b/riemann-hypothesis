module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0051
public import Development.EtaleCohomology.EtaleSheaves.Bundle0048
public import Development.EtaleCohomology.EtaleSheaves.Bundle0045

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelEqvInjPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.RelEqvInjPf

set_option linter.unusedSectionVars false
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

abbrev pl {K L : CochainComplex C ℤ} (f : K ⟶ L) (M : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass L M n →+ CohomologyClass K M n := cpre (Cocycle.ofHom f) M n n (zero_add n)

lemma inr_map {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) : mappingCone.inr φ' ≫ mappingCone.map φ' φ α β comm = β ≫ mappingCone.inr φ := by
  simp [mappingCone.map]

lemma map_fst {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) :
    (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp (mappingCone.fst φ).1 (zero_add 1) =
      (mappingCone.fst φ').1.comp (Cochain.ofHom α) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_zero 1) (by omega)]
    simp [mappingCone.map]
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain]
    simp

lemma laurent_adjoin_eq_of_image_eq {A' A I : CochainComplex C ℤ} (α : A' ⟶ A) {j k : ℤ} (hjk : j + 1 = k)
    (hα : Function.Injective (pl α I k)) (z : Cocycle A I k) (ξ : Cochain A' I j)
    (h : δ j k ξ = (Cochain.ofHom α).comp z.1 (zero_add k)) : ∃ t : Cochain A I j, δ j k t = z.1 := by
  have h0 : pl α I k (CohomologyClass.mk z) = 0 := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom α) z (zero_add k)) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨j, hjk, ξ, h⟩
  have h1 : CohomologyClass.mk z = 0 := hα (h0.trans (map_zero _).symm)
  rw [CohomologyClass.mk_eq_zero_iff] at h1
  obtain ⟨j', hj', t, ht⟩ := h1
  obtain rfl : j' = j := by omega
  exact ⟨t, ht⟩

lemma exists_finset_adjoin_laurent_preimage {B' B I : CochainComplex C ℤ} (β : B' ⟶ B) {j k : ℤ} (hjk : j + 1 = k)
    (hβ : Function.Surjective (pl β I k)) (z : Cocycle B' I k) :
    ∃ (w : Cocycle B I k) (r : Cochain B' I j), δ j k r = z.1 - (Cochain.ofHom β).comp w.1 (zero_add k) := by
  obtain ⟨W, hW⟩ := hβ (CohomologyClass.mk z)
  obtain ⟨w, rfl⟩ := W.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom β) w (zero_add k)) = _ at hW
  have h2 := hW.symm
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at h2
  obtain ⟨j', hj', r, hr⟩ := h2
  obtain rfl : j' = j := by omega
  exact ⟨w, r, by rw [hr]; rfl⟩

theorem main {A B A' B' I : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) (l m n : ℤ) (hl : l + 1 = m) (hm : m + 1 = n)
    (hαi : Function.Injective (pl α I m)) (hβi : Function.Injective (pl β I n))
    (hβs : Function.Surjective (pl β I m)) :
    Function.Injective (pl (mappingCone.map φ' φ α β comm) I n) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp _ c _) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m', hm', ξ0, hξ0⟩ := hy
  have em : m' = m := by omega
  subst m'
  change δ m n ξ0 = (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp c.1 (zero_add n) at hξ0
  set a := (mappingCone.inl φ).comp c.1 (show -1 + n = m by omega) with ha
  set b := (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add n) with hb
  have hdec : c.1 = mappingCone.descCochain φ a b hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm]; simp [ha, hb]
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hδa : δ m n a = n.negOnePow • (Cochain.ofHom φ).comp b (zero_add n) := by
    have h := congrArg (fun z => (mappingCone.inl φ).comp z (show -1 + (n + 1) = n by omega)) hc
    simp only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] at h
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  have hδb : δ n (n + 1) b = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (n + 1))) hc
    simpa using h

  have h1 : δ m n ((Cochain.ofHom (mappingCone.inr φ')).comp ξ0 (zero_add m)) =
      (Cochain.ofHom β).comp (Cocycle.mk b (n + 1) rfl hδb).1 (zero_add n) := by
    rw [δ_ofHom_comp, hξ0, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    rfl
  obtain ⟨η, hη⟩ := laurent_adjoin_eq_of_image_eq β hm hβi _ _ h1
  change δ m n η = b at hη

  set s := n.negOnePow with hs
  set γ := a - s • (Cochain.ofHom φ).comp η (zero_add m) with hγ
  have hδγ : δ m n γ = 0 := by
    rw [hγ, δ_sub, δ_units_smul, δ_ofHom_comp, hη, hδa, sub_self]
  set D0 := mappingCone.descCochain φ (0 : Cochain A I l) η hl with hD0
  have hcγ : c.1 = δ m n D0 + (mappingCone.fst φ).1.comp γ (by omega) := by
    rw [hdec, hD0, mappingCone.δ_descCochain _ _ _ _ _ hm, hη, hγ]
    simp only [mappingCone.descCochain, δ_zero, zero_add, Cochain.comp_sub]
    abel

  set ξ := ξ0 - (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp D0 (zero_add m) with hξ
  have h3 : δ m n ξ = (mappingCone.fst φ').1.comp ((Cochain.ofHom α).comp γ (zero_add m)) (by omega) := by
    rw [hξ, δ_sub, δ_ofHom_comp, hξ0, hcγ, Cochain.comp_add, add_sub_cancel_left,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, map_fst, Cochain.comp_assoc_of_second_is_zero_cochain]
  set p := (mappingCone.inl φ').comp ξ (show -1 + m = l by omega) with hp
  set q := (Cochain.ofHom (mappingCone.inr φ')).comp ξ (zero_add m) with hq
  have hdecξ : ξ = mappingCone.descCochain φ' p q hl := by
    rw [mappingCone.ext_cochain_from_iff _ l m hl]; simp [hp, hq]
  rw [hdecξ, mappingCone.δ_descCochain _ _ _ _ _ hm] at h3
  have h3a : δ l m p + s • (Cochain.ofHom φ').comp q (zero_add m) = (Cochain.ofHom α).comp γ (zero_add m) := by
    have h := congrArg (fun z => (mappingCone.inl φ').comp z (show -1 + n = m by omega)) h3
    simpa only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] using h
  have h3b : δ m n q = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ')).comp z (zero_add n)) h3
    simpa using h

  obtain ⟨w, r, hr⟩ := exists_finset_adjoin_laurent_preimage β hl hβs (Cocycle.mk q n hm h3b)
  change δ l m r = q - (Cochain.ofHom β).comp w.1 (zero_add m) at hr
  have hw : δ m n w.1 = 0 := Cocycle.δ_eq_zero w n
  have h4 : δ l m (p + s • (Cochain.ofHom φ').comp r (zero_add l)) =
      (Cochain.ofHom α).comp (Cocycle.mk (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) n hm
        (by rw [δ_sub, δ_units_smul, δ_ofHom_comp, hδγ, hw]; simp)).1 (zero_add m) := by
    change _ = (Cochain.ofHom α).comp (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) (zero_add m)
    rw [δ_add, δ_units_smul, δ_ofHom_comp, hr, Cochain.comp_sub, Cochain.comp_sub, ← h3a,
      Cochain.comp_units_smul]
    simp only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
    rw [comm, smul_sub]
    abel
  obtain ⟨t, ht⟩ := laurent_adjoin_eq_of_image_eq α hl hαi _ _ h4
  change δ l m t = γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m) at ht

  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, D0 + mappingCone.descCochain φ t w.1 hl, ?_⟩
  rw [δ_add, mappingCone.δ_descCochain φ t w.1 hl n hm, ht, hw, hcγ]
  simp
  rw [← hs, sub_add_cancel]

theorem RelEqvInj_of : LateralTheory.E.RelDescPf.RelEqvInj := by
  intro R _ F U E U' E' f f' u e comm hu he n
  exact main ((chains R).map f) ((chains R).map f') ((chains R).map u) ((chains R).map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (n - 1 - 1) (n - 1) n (by omega) (by omega)
    (hu (n - 1)).1 (he n).1 (he (n - 1)).2

end LateralTheory.E.RelEqvInjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) :
    pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s := pullback.fst _ _

abbrev tY {Y B S : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) (t : S ⟶ U.left) : pullback p (t ≫ U.hom) ⟶ YU p U :=
  pullback.map p (t ≫ U.hom) p U.hom (𝟙 Y) t (𝟙 B) (by simp) (by simp)

abbrev tW {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) :
    pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (tY p U t) (𝟙 W) (𝟙 B) (by simp only [tY, pullback.lift_snd_assoc, Category.assoc]; erw [Category.comp_id]) (by simp)

abbrev rT (q : ℕ) (i : ℤ) {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prS p ι (t ≫ U.hom)) (tW p ι U t) (tY p U t) (pullback.lift_fst _ _ _).symm m

def LeafKillPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → rT q i p ι U t m z = 0) →
  Cov U (fun _ a => rY q i p ι a m z = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → ¬ (Set.range s ⊆ V) →
  ∀ m, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y Y' : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B) (g : Y' ⟶ Y), IsProper p → IsProper (g ≫ p) → ∀ (U : B.Etale) (A : Type) [CommRing A]
  (t : Sp A ⟶ U.left), SH A → Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B) → ∀ (m : ℤ), pl q i (fibMap g p (t ≫ U.hom)) m = 0 →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, rT q i (g ≫ p) ι U t m (gY q i p g ι U m y) = 0

theorem LeafKill2_of (hPt : LeafKillPt) (hW : LeafPtW) (hV : LeafPtV) : LeafKill2 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 toK ι _ V hVW p g1 g2 hp hp1 hp2 hS U y
  refine hPt hH q k hq i toK ι (g1 ≫ p) hp1 U 2 _ ?_
  intro A _ t hA
  by_cases hc : Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B)
  · exact hV hH q k hq i toK ι V hVW p g1 hp hp1 U A t hA hc 2 (hS A (t ≫ U.hom) hA hc).2.1 y
  · have := hW hH q k hq i toK ι V hVW (g1 ≫ p) hp1 A (t ≫ U.hom) hA hc 2
    exact Subsingleton.elim _ _

end LateralTheory.E.SecondDegreeKilling
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShIsoPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves

theorem Cov.bind {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' (a : U' ⟶ U), P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : Sieve U :=
    { arrows := fun Z c => ∀ (W : B.Etale) (d : W ⟶ Z), Q W (d ≫ c)
      downward_closed := fun {Z Z'} c hc e W d => by simpa [Category.assoc] using hc W (d ≫ e) }
  refine ⟨R, (EtTop B).transitive hS R ?_, fun U' a ha => by simpa using ha U' (𝟙 _)⟩
  intro Y f hf
  obtain ⟨S', hS', hQ⟩ := hPQ Y f (hP Y f hf)
  refine (EtTop B).superset_covering ?_ hS'
  intro Z c hc W d
  simpa [Category.assoc] using hQ W (d ≫ c) (S'.downward_closed hc d)

abbrev H0 (B : Scheme.{0}) (q : ℕ) := DerivedCategory.homologyFunctor (SShv B q) 0

def EtaleDerivedDegreeZeroHomologyLocallyLifts : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (t : (H0 B q).obj ((OU B q).obj U) ⟶ (H0 B q).obj M),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ M, (H0 B q).map ((OU B q).map a) ≫ t = (H0 B q).map x)

def EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (M : DerivedCategory (SShv B q)) (U : B.Etale)
  (x : (OU B q).obj U ⟶ M), (H0 B q).map x = 0 → Cov U (fun U' a => (OU B q).map a ≫ x = 0)

def LeafSheafIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (F G : SShv B q) (g : F ⟶ G),
  (∀ (U : B.Etale) (t : (H0 B q).obj ((OU B q).obj U) ⟶ F), t ≫ g = 0 →
    Cov U (fun U' a => (H0 B q).map ((OU B q).map a) ≫ t = 0)) →
  (∀ (U : B.Etale) (s : (H0 B q).obj ((OU B q).obj U) ⟶ G),
    Cov U (fun U' a => ∃ t : (H0 B q).obj ((OU B q).obj U') ⟶ F, (H0 B q).map ((OU B q).map a) ≫ s = t ≫ g)) →
  IsIso g

theorem LeafShIso_of (hL : EtaleDerivedDegreeZeroHomologyLocallyLifts) (hK : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes) (hS : LeafSheafIso) : LeafShIso := by
  intro B q L K ℓ m hinj hsurj
  set f := (shiftFunctor (DerivedCategory (SShv B q)) m).map ℓ with hf
  have key : IsIso ((H0 B q).map f) := by
    apply hS
    · intro U t ht
      refine Cov.bind (hL B q _ U t) ?_
      rintro U' a ⟨x, hx⟩
      have h1 : (H0 B q).map (x ≫ f) = 0 := by
        rw [Functor.map_comp, ← hx, Category.assoc, ht, comp_zero]
      have h2 := hinj U' x 0 ((hK B q _ U' _ h1).mono (fun U'' b hb => by simpa using hb))
      refine h2.mono (fun U'' b hb => ?_)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hx, ← Functor.map_comp, hb, comp_zero,
        Functor.map_zero]
    · intro U s
      refine Cov.bind (hL B q _ U s) ?_
      rintro U' a ⟨y, hy⟩
      refine (hsurj U' y).mono (fun U'' b ⟨x, hx⟩ => ⟨(H0 B q).map x, ?_⟩)
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, hy, ← Functor.map_comp, hx, Functor.map_comp]
  have e := ((H0 B q).isoShift m)
  exact (NatIso.isIso_map_iff e ℓ).1 key

end LateralTheory.E.LeafShIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SimplicialPieceRelations
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf

namespace LateralTheory.E.SimplicialPieceRelations

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)
abbrev HC (R : Type) [CommRing R] := HomotopyCategory (Shv R) (ComplexShape.up ℤ)

def Disc0 : Prop := ∀ (R : Type) [CommRing R] {X Y : PSh} (f : X ⟶ Y),
  ∃ (a : (Qt R).obj ((chains R).obj (disc.obj X)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj X)))
    (b : (Qt R).obj ((chains R).obj (disc.obj Y)) ≅ (Qt R).obj ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj Y))),
    (Qt R).map ((chains R).map (disc.map f)) ≫ b.hom = a.hom ≫ (Qt R).map ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f))

variable {R : Type} [CommRing R]

theorem relY_conj_imp (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g → Tri.RelY (Yres R F) n g' := by
  have hg' : g' = a.inv ≫ g ≫ b.hom := by rw [h]; simp
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨x, hx⟩ := hs (a.hom ≫ y)
    refine ⟨b.inv ≫ x, ?_⟩
    simp only at hx ⊢
    rw [hg']; simp [hx]
  · simp only at hx
    rw [hg'] at hx
    have : g ≫ (b.hom ≫ x1) = g ≫ (b.hom ≫ x2) := by
      have := congrArg (fun z => a.hom ≫ z) hx
      simpa using this
    have := hi this
    simpa using congrArg (fun z => b.inv ≫ z) this

theorem relY_conj (F : Shv R) (n : ℤ) {A B A' B' : HC R} (g : A ⟶ B) (g' : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : g ≫ b.hom = a.hom ≫ g') : Tri.RelY (Yres R F) n g ↔ Tri.RelY (Yres R F) n g' :=
  ⟨relY_conj_imp F n g g' a b h, relY_conj_imp F n g' g a.symm b.symm (by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h]; simp)⟩

def yIso (F : Shv R) (p m c : ℤ) (hc : m + p = c) : Yres R F c ≅ (Yres R F m)⟦p⟧ :=
  (Qt R).mapIso ((shiftFunctorAdd' (Cx R) m p c hc).app (res R F)) ≪≫ ((Qt R).commShiftIso p).app _

theorem relY_shift (F : Shv R) (k p : ℤ) {A B : HC R} (g : A ⟶ B) :
    Tri.RelY (Yres R F) k g → Tri.RelY (Yres R F) (k + p) (g⟦p⟧') := by
  rintro ⟨hs, hi⟩
  refine ⟨fun y => ?_, fun x1 x2 hx => ?_⟩
  · let e := yIso F p (k - 1) (k + p - 1) (by omega)
    obtain ⟨z, hz⟩ := (shiftFunctor (HC R) p).map_surjective (y ≫ e.hom)
    obtain ⟨w, hw⟩ := hs z
    refine ⟨(shiftFunctor (HC R) p).map w ≫ e.inv, ?_⟩
    simp only at hw ⊢
    rw [← Category.assoc, ← Functor.map_comp, hw, hz]; simp
  · let e := yIso F p k (k + p) rfl
    obtain ⟨w1, hw1⟩ := (shiftFunctor (HC R) p).map_surjective (x1 ≫ e.hom)
    obtain ⟨w2, hw2⟩ := (shiftFunctor (HC R) p).map_surjective (x2 ≫ e.hom)
    simp only at hx
    have h1 : (shiftFunctor (HC R) p).map (g ≫ w1) = (shiftFunctor (HC R) p).map (g ≫ w2) := by
      rw [Functor.map_comp, Functor.map_comp, hw1, hw2, ← Category.assoc, ← Category.assoc, hx]
    have h2 := hi ((shiftFunctor (HC R) p).map_injective h1)
    have : x1 ≫ e.hom = x2 ≫ e.hom := by rw [← hw1, ← hw2, h2]
    simpa using congrArg (fun z => z ≫ e.inv) this

theorem chains_f (U E : Spc) (u : U ⟶ E) (p : ℕ) :
    ((chains R).map u).f (-(p : ℤ)) =
      (chainsXIso R U p).hom ≫ (free R).map (u.app (Opposite.op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  dsimp only [chains, chainsXIso, Functor.comp_map]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl]
  rfl

theorem piece_of (hD : Disc0) : Piece := by
  intro R _ F U E u p k h
  let f := u.app (Opposite.op (SimplexCategory.mk p))
  let s0 := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)
  have h1 : Tri.RelY (Yres R F) k ((Qt R).map ((chains R).map (disc.map f))) := (relK_iff R _ F k).1 h
  obtain ⟨a, b, hab⟩ := hD R f
  have h2 : Tri.RelY (Yres R F) k ((Qt R).map s0) := (relY_conj F k _ _ a b hab).1 h1
  have h3 := relY_shift F k (p : ℤ) _ h2
  have h4 : Tri.RelY (Yres R F) (k + p) ((Qt R).map (s0⟦(p : ℤ)⟧')) :=
    (relY_conj F _ _ _ (((Qt R).commShiftIso (p : ℤ)).app _) (((Qt R).commShiftIso (p : ℤ)).app _)
      (((Qt R).commShiftIso (p : ℤ)).hom.naturality s0)).2 h3
  let Eo := (CochainComplex.singleFunctors (Shv R)).shiftIso (p : ℤ) (-(p : ℤ)) 0 (by omega)
  have h5 : Tri.RelY (Yres R F) (k + p) ((Qt R).map ((CochainComplex.singleFunctor (Shv R) (-(p : ℤ))).map ((free R).map f))) :=
    (relY_conj F _ _ _ ((Qt R).mapIso (Eo.symm.app _)) ((Qt R).mapIso (Eo.symm.app _)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact Eo.inv.naturality _)).2 h4
  refine (relK_iff R _ F (k + p)).2 ?_
  refine (relY_conj F _ _ _ ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R U p)))
    ((Qt R).mapIso ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))) ?_).2 h5
  simp only [piece, Functor.mapIso_hom, ← Functor.map_comp, chains_f]
  simp [f]
  rfl

end LateralTheory.E.SimplicialPieceRelations
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkAICRingPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StalkAICRingPf

theorem aic_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : AIC R) : AIC S := by
  intro p hp hn
  rcases subsingleton_or_nontrivial R with hR1 | hR1
  · refine ⟨0, ?_⟩
    have h01 : (0 : S) = 1 := by
      rw [← map_zero (algebraMap R S), ← map_one (algebraMap R S), Subsingleton.elim (0 : R) 1]
    exact @Subsingleton.elim _ (subsingleton_of_zero_eq_one h01) _ _
  set n := p.natDegree with hnd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples M (Finset.univ : Finset (Fin n)) (fun i => p.coeff i)
  choose r hr using fun i : Fin n => hb i (Finset.mem_univ _)
  set β : S := algebraMap R S b with hβ
  have hu : IsUnit β := IsLocalization.map_units S b
  set q : R[X] := X ^ n + ∑ i : Fin n, C (r i * (b : R) ^ (n - 1 - i)) * X ^ (i : ℕ) with hq
  have hqm : q.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hqd : q.natDegree = n := by
    rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact degree_sum_fin_lt _
  obtain ⟨c, hc⟩ := hR q hqm (hqd ▸ hn)
  refine ⟨hu.unit⁻¹ * algebraMap R S c, ?_⟩
  have key : β ^ n * p.eval (hu.unit⁻¹ * algebraMap R S c) = algebraMap R S (q.eval c) := by
    conv_lhs => rw [hp.as_sum]
    rw [← hnd, ← Fin.sum_univ_eq_sum_range]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add (f := _), map_pow, map_sum, map_mul, mul_add,
      Finset.mul_sum]
    congr 1
    · rw [← mul_pow, ← mul_assoc, hu.mul_val_inv, one_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i]
      have hβn : β ^ n = β ^ 1 * β ^ (n - 1 - (i : ℕ)) * β ^ (i : ℕ) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      simp only [Algebra.smul_def, ← hβ]
      rw [hβn, mul_pow]
      have h1 : β ^ (i : ℕ) * (↑hu.unit⁻¹ : S) ^ (i : ℕ) = 1 := by rw [← mul_pow, hu.mul_val_inv, one_pow]
      linear_combination (β ^ 1 * β ^ (n - 1 - (i:ℕ)) * p.coeff i * algebraMap R S c ^ (i:ℕ)) * h1
  rw [hc, map_zero] at key
  exact (hu.pow n).mul_right_eq_zero.1 key

theorem StalkAICRing_of : LateralTheory.E.FibreEqvPf.StalkAICRing := by
  intro S hS x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let _ := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact aic_loc (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (hS.2 U hU ⟨x, hxU⟩)

end LateralTheory.E.StalkAICRingPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafShMapZeroPf
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem Cov.trans {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Cov U' (fun U'' b => Q U'' (b ≫ a))) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y : B.Etale⦄ ⦃f : Y ⟶ U⦄, S f → Sieve Y := fun Y f hf =>
    Classical.choose (hPQ Y f (hP Y f hf))
  refine ⟨Sieve.bind S R, (EtTop B).bind_covering hS
    (fun Y f hf => (Classical.choose_spec (hPQ Y f (hP Y f hf))).1), ?_⟩
  rintro U'' _ ⟨Y, g, f, hf, hg, rfl⟩
  exact (Classical.choose_spec (hPQ Y f (hP Y f hf))).2 U'' g hg

def EtaleLift' : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K : DerivedCategory (SShv B q)) (U : B.Etale)
  (s : (DerivedCategory.homologyFunctor (SShv B q) 0).obj ((OU B q).obj U) ⟶
    (DerivedCategory.homologyFunctor (SShv B q) 0).obj K),
  Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ K,
    (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x)

def LeafGen : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (H H' : SShv B q) (g : H ⟶ H'),
  (∀ (U : B.Etale) (s : (DerivedCategory.homologyFunctor (SShv B q) 0).obj ((OU B q).obj U) ⟶ H),
    Cov U (fun U' a => (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s ≫ g = 0)) → g = 0

theorem zero_of (hA : EtaleLift') (hB : LeafGen) (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q))
    (f : K ⟶ K')
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ K), Cov U (fun U' a => (OU B q).map a ≫ x ≫ f = 0)) :
    (DerivedCategory.homologyFunctor (SShv B q) 0).map f = 0 := by
  apply hB B q _ _ _
  intro U s
  refine Cov.trans (hA B q K U s) ?_
  rintro U' a ⟨x, hx⟩
  refine (h U' x).mono fun U'' b hb => ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, reassoc_of% hx, ← Functor.map_comp,
    ← Functor.map_comp, hb, Functor.map_zero]

theorem LeafShMapZero_of (hA : EtaleLift') (hB : LeafGen) : LeafShMapZero := by
  intro B q K K' f m h
  have h0 := zero_of hA hB B q _ _ ((shiftFunctor _ m).map f) h
  have e := (DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shiftIso_hom_naturality m (0 : ℤ) m (by simp) f
  have h0' : ((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shift (0 : ℤ)).map
      ((shiftFunctor _ m).map f) = 0 := h0
  change ((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shift m).map f = 0
  rw [← cancel_epi (((DerivedCategory.homologyFunctor (SShv B q) (0 : ℤ)).shiftIso m (0 : ℤ) m (by simp)).hom.app K),
    comp_zero, ← e, h0', zero_comp]

end LateralTheory.E.LeafShMapZeroPf
end
end


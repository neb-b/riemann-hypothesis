module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.EtaleSheaves.Bundle0004

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LineOneCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def Charts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

def ChartSurj : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
    w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
      pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b

theorem goal_of (hMV : MV) (hC : Charts) (hF : FibCover) (hA : ChartAcyc) (hS : ChartSurj) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := hS H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.LineOneCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LineZeroCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineZeroCut

def LZNonempty : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)),
  UniversallyClosed p → Nonempty X → Nonempty ↑(pullback p (cpt A))

theorem lzNonempty : LZNonempty := by
  intro A _ _ X p hp hX
  obtain ⟨x⟩ := hX
  have hc : IsClosed (Set.range p.base) := p.isClosedMap.isClosed_range
  have h1 : IsLocalRing.closedPoint A ∈ Set.range p.base := by
    have : IsLocalRing.closedPoint A ∈ closure {p.base x} :=
      (PrimeSpectrum.le_iff_mem_closure _ _).1 (IsLocalRing.le_maximalIdeal (p.base x).isPrime.ne_top)
    exact closure_minimal (by simp) hc this
  obtain ⟨z, hz⟩ := h1
  have h2 : (cpt A) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) = IsLocalRing.closedPoint A :=
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom (IsLocalRing.residue A))) :=
      (inferInstance : IsLocalHom (IsLocalRing.residue A))
    Spec_closedPoint
  obtain ⟨w, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := cpt A) z
    (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) (by rw [hz, h2])
  exact ⟨w⟩

end LateralTheory.E.LineZeroCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocDiagPf
section
noncomputable section
open CategoryTheory Limits Opposite

namespace LateralTheory.E.LocDiagPf


open Classical in
def g {S : Type} [CommRing S] (p : PrimeSpectrum S) (s : Finset p.asIdeal.primeCompl) : S :=
  ∏ x ∈ s, (x : S)

variable {S : Type} [CommRing S] (p : PrimeSpectrum S)

theorem g_mem (s : Finset p.asIdeal.primeCompl) : g p s ∈ p.asIdeal.primeCompl := by
  classical
  unfold g
  convert Submonoid.prod_mem _ (fun (x : p.asIdeal.primeCompl) _ => x.2)

theorem g_dvd {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) : g p s ∣ g p t := by
  classical
  unfold g
  convert Finset.prod_dvd_prod_of_subset s t (fun x : p.asIdeal.primeCompl => (x : S)) h

theorem g_single (y : p.asIdeal.primeCompl) : g p {y} = (y : S) := by
  classical
  unfold g
  convert Finset.prod_singleton (fun x : p.asIdeal.primeCompl => (x : S)) y

theorem unitAway {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    IsUnit (algebraMap S (Localization.Away (g p t)) (g p s)) :=
  isUnit_of_dvd_unit (map_dvd _ (g_dvd p h)) (IsLocalization.Away.algebraMap_isUnit _)

def tr {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    Localization.Away (g p s) →+* Localization.Away (g p t) :=
  IsLocalization.Away.lift (g p s) (unitAway p h)

theorem tr_comp {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    (tr p h).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem tr_apply {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) (x : S) :
    tr p h (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

theorem away_ext {s : Finset p.asIdeal.primeCompl} {P : Type} [CommRing P]
    {u v : Localization.Away (g p s) →+* P}
    (h : u.comp (algebraMap S _) = v.comp (algebraMap S _)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers (g p s)) h

def Dg : Finset p.asIdeal.primeCompl ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (g p s))
  map {s t} h := CommRingCat.ofHom (tr p (leOfHom h))
  map_id s := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, tr_comp]
    rfl
  map_comp {s t u} a b := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, tr_comp, tr_comp, tr_comp]

theorem unitLoc (s : Finset p.asIdeal.primeCompl) :
    IsUnit (algebraMap S (Localization.AtPrime p.asIdeal) (g p s)) :=
  IsLocalization.map_units _ (⟨g p s, g_mem p s⟩ : p.asIdeal.primeCompl)

def toLoc (s : Finset p.asIdeal.primeCompl) :
    Localization.Away (g p s) →+* Localization.AtPrime p.asIdeal :=
  IsLocalization.Away.lift (g p s) (unitLoc p s)

theorem toLoc_comp (s : Finset p.asIdeal.primeCompl) :
    (toLoc p s).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem toLoc_apply (s : Finset p.asIdeal.primeCompl) (x : S) :
    toLoc p s (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

def Cc : Cocone (Dg p) where
  pt := CommRingCat.of (Localization.AtPrime p.asIdeal)
  ι :=
    { app := fun s => (CommRingCat.ofHom (toLoc p s) : (Dg p).obj s ⟶ CommRingCat.of (Localization.AtPrime p.asIdeal))
      naturality := fun s t h => by
        ext1
        apply away_ext
        simp only [Functor.const_obj_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom, Dg]
        rw [RingHom.comp_assoc, tr_comp, toLoc_comp, RingHom.comp_assoc, toLoc_comp]
        rfl }

def phi (c : Cocone (Dg p)) : S →+* c.pt :=
  (c.ι.app ∅).hom.comp (algebraMap S (Localization.Away (g p ∅)))

theorem cocone_comp (c : Cocone (Dg p)) (s : Finset p.asIdeal.primeCompl) :
    (c.ι.app s).hom.comp (algebraMap S (Localization.Away (g p s))) = phi p c := by
  have hw := c.w (homOfLE (Finset.empty_subset s))
  unfold phi
  rw [← hw]
  ext x
  exact congrArg (c.ι.app s).hom (tr_apply p (Finset.empty_subset s) x).symm

theorem phi_unit (c : Cocone (Dg p)) (y : p.asIdeal.primeCompl) : IsUnit (phi p c y) := by
  rw [← DFunLike.congr_fun (cocone_comp p c {y}) (y : S)]
  have hy : IsUnit (algebraMap S (Localization.Away (g p {y})) y) := by
    rw [show (y : S) = g p {y} from (g_single p y).symm]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact IsUnit.map (c.ι.app {y}).hom hy

def isColim : IsColimit (Cc p) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := p.asIdeal.primeCompl)
    (S := Localization.AtPrime p.asIdeal) (phi_unit p c))
  fac c s := by
    ext1
    apply away_ext
    ext x
    change (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (toLoc p s (algebraMap S _ x)) =
      (c.ι.app s).hom (algebraMap S (Localization.Away (g p s)) x)
    rw [toLoc_apply, IsLocalization.lift_eq]
    exact (DFunLike.congr_fun (cocone_comp p c s) x).symm
  uniq c m hm := by
    ext1
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl ?_
    ext x
    have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hm ∅))
      (algebraMap S (Localization.Away (g p ∅)) x)
    change m.hom (algebraMap S (Localization.AtPrime p.asIdeal) x) =
      (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (algebraMap S _ x)
    rw [IsLocalization.lift_eq]
    refine Eq.trans ?_ hx
    change _ = m.hom (toLoc p ∅ (algebraMap S _ x))
    rw [toLoc_apply]

theorem LocDiag_of : LateralTheory.E.ZarLocalPf.LocDiag := by
  intro S _ p
  refine ⟨Finset p.asIdeal.primeCompl, inferInstance, inferInstance, Dg p, Cc p,
    ⟨isColim p⟩, id, ∅, algebraMap S (Localization.Away (g p ∅)), ?_⟩
  intro k m
  refine ⟨g p k, g_mem p k, RingHom.id _, ?_⟩
  ext x
  exact tr_apply p (leOfHom m) x

end LateralTheory.E.LocDiagPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSHPf
section
noncomputable section
open Polynomial IsLocalRing GlobalTheory.EtC

namespace LateralTheory.E.LocSHPf

theorem aic_localization (S : Type) [CommRing S] (hS : AIC S) (M : Submonoid S) (R : Type) [CommRing R]
    [Algebra S R] [IsLocalization M R] : AIC R := by
  intro P hP hd
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M ((Finset.range (P.natDegree + 1)).image P.coeff)
  set s : R := algebraMap S R (b : S) with hs
  have hlift : P.scaleRoots s ∈ lifts (algebraMap S R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨y, hy⟩ := hb (P.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      refine ⟨y * (b : S) ^ k, ?_⟩
      rw [map_mul, map_pow, hy, hk, pow_succ, Algebra.smul_def, ← hs]
      ring
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by rw [map_one]; exact hP.symm⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact ⟨0, map_zero _⟩
  have hmon : (P.scaleRoots s).Monic := by
    rw [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]; exact hP
  obtain ⟨Q, hQ, hQd, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hmon
  obtain ⟨a, ha⟩ := hS Q hQm (by rw [hQd, natDegree_scaleRoots]; exact hd)
  have hu : IsUnit s := IsLocalization.map_units R b
  refine ⟨hu.unit⁻¹ * algebraMap S R a, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := P) (RingHom.id R) (hu.unit⁻¹ * algebraMap S R a) s
  have h2 : s * (hu.unit⁻¹ * algebraMap S R a) = algebraMap S R a := by
    rw [← mul_assoc, hu.mul_val_inv, one_mul]
  rw [RingHom.id_apply, h2, ← eval, ← eval, ← hQ, eval_map, eval₂_hom, ha, map_zero] at h1
  have := (hu.pow P.natDegree).mul_right_eq_zero.1 h1.symm
  exact this

theorem root_near (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) (a₀ : R) :
    ∀ n : ℕ, ∀ f : R[X], f.natDegree = n → f.Monic → f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  intro n
  induction n with
  | zero =>
    intro f hn hf he
    rw [eq_one_of_monic_natDegree_zero hf hn, eval_one] at he
    exact absurd he (Ideal.IsMaximal.ne_top inferInstance |> fun h => fun h1 => h ((Ideal.eq_top_iff_one _).2 h1))
  | succ n ih =>
    intro f hn hf he
    obtain ⟨a, ha⟩ := hR f hf (by omega)
    have hfac := (mul_divByMonic_eq_iff_isRoot (p := f) (a := a)).2 ha
    have hgm : (f /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hf)
    have hgd : (f /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at he
    rcases Ideal.IsPrime.mem_or_mem (inferInstance : (maximalIdeal R).IsPrime) he with h | h
    · refine ⟨a, ha, ?_⟩
      rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h
    · obtain ⟨b, hb, hb'⟩ := ih _ hgd hgm h
      refine ⟨b, ?_, hb'⟩
      rw [← hfac, IsRoot, eval_mul, hb.eq_zero, mul_zero]

theorem henselian_of_aic (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : HenselianLocalRing R where
  is_henselian f hf a₀ he _ := root_near R hR a₀ _ f rfl hf he

theorem residue_algClosed (R : Type) [CommRing R] [IsLocalRing R] (hR : AIC R) : IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hl : p ∈ lifts (residue R) := by
    rw [lifts_iff_coeff_lifts]; intro n; exact residue_surjective _
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hp
  have hpos : 0 < p.natDegree := natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)
  obtain ⟨a, ha⟩ := hR q hqm (by omega)
  exact ⟨residue R a, by rw [← hq, eval_map, eval₂_hom, ha, map_zero]⟩

theorem LocSH_of : LateralTheory.E.ZarLocalPf.LocSH := by
  intro S _ hS p
  have hA := aic_localization S hS p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  have := residue_algClosed _ hA
  exact ⟨henselian_of_aic _ hA, inferInstance⟩

end LateralTheory.E.LocSHPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.MVSpcPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.MVSpcPf

def Ses : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

variable {R : Type} [CommRing R] {I : Cx R}

abbrev pc {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : Cochain K I m := (Cochain.ofHom φ).comp z (zero_add m)

theorem pc_comp {K L M : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {m : ℤ} (z : Cochain M I m) : pc (φ ≫ ψ) z = pc φ (pc ψ z) := by
  simp [pc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem pc_addm {K L : Cx R} (φ ψ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (φ + ψ) z = pc φ z + pc ψ z := by
  simp [pc, Cochain.ofHom_add, Cochain.add_comp]

theorem pc_negm {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (-φ) z = -pc φ z := by
  simp [pc, Cochain.ofHom_neg, Cochain.neg_comp]

theorem pc_zerom {K L : Cx R} {m : ℤ} (z : Cochain L I m) : pc (0 : K ⟶ L) z = 0 := by
  simp [pc, Cochain.ofHom_zero, Cochain.zero_comp]

theorem pc_add {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z + z') = pc φ z + pc φ z' := by
  simp [pc, Cochain.comp_add]

theorem pc_sub {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z - z') = pc φ z - pc φ z' := by
  simp [pc, Cochain.comp_sub]

theorem pc_δ {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) (m' : ℤ) : δ m m' (pc φ z) = pc φ (δ m m' z) :=
  δ_ofHom_comp φ z m'

theorem cpre_mk' {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cocycle L I m) :
    cpre (Cocycle.ofHom φ) I m m (zero_add m) (CohomologyClass.mk z) =
      CohomologyClass.mk (Cocycle.mk (pc φ z.1) (m + 1) rfl (by rw [pc_δ, Cocycle.δ_eq_zero, pc, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

theorem cocy_δ {K : Cx R} {m : ℤ} (z : Cocycle K I m) (m' : ℤ) : δ m m' z.1 = 0 := by
  by_cases h : m + 1 = m'
  · exact (Cocycle.mem_iff m m' h z.1).1 z.2
  · exact δ_shape _ _ h _

theorem chase (hI : ∀ n, Injective (I.X n)) {K1 KA KB K3 : Cx R} (φ : K1 ⟶ KA) (ψ : K1 ⟶ KB) (u : KA ⟶ K3)
    (v : KB ⟶ K3) (w) (hS : (ShortComplex.mk (biprod.lift φ (-ψ)) (biprod.desc u v) w).ShortExact) (n : ℤ)
    (hc : ∀ c : CohomologyClass K1 I n, ∃ a b, c = cpre (Cocycle.ofHom φ) I n n (zero_add n) a -
      cpre (Cocycle.ofHom ψ) I n n (zero_add n) b)
    (x : CohomologyClass K3 I (n + 1)) (hu : cpre (Cocycle.ofHom u) I _ _ (zero_add _) x = 0)
    (hv : cpre (Cocycle.ofHom v) I _ _ (zero_add _) x = 0) : x = 0 := by
  have hC := fun m => LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds R I hI _ hS m
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [cpre_mk', CohomologyClass.mk_eq_zero_iff] at hu hv
  obtain ⟨m, hm, aU, haU⟩ := hu
  obtain ⟨m', hm', aV, haV⟩ := hv
  have e1 : n = m := by omega
  subst e1
  have e2 : n = m' := by omega
  subst e2
  simp only [Cocycle.mk_coe] at haU haV
  set b : Cochain (KA ⊞ KB) I n := pc biprod.fst aU + pc biprod.snd aV with hbdef
  have hb : δ n (n + 1) b = pc (biprod.desc u v) z.1 := by
    rw [hbdef, δ_add, pc_δ, pc_δ, haU, haV, ← pc_comp, ← pc_comp, ← pc_addm, ← biprod.desc_eq]
  have hαb : δ n (n + 1) (pc (biprod.lift φ (-ψ)) b) = 0 := by
    rw [pc_δ, hb, ← pc_comp, w, pc_zerom]
  obtain ⟨a, b0, hab⟩ := hc (CohomologyClass.mk (Cocycle.mk (pc (biprod.lift φ (-ψ)) b) (n + 1) rfl hαb))
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b0, rfl⟩ := b0.mk_surjective
  rw [cpre_mk', cpre_mk', ← CohomologyClass.mk_sub, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff] at hab
  obtain ⟨k, hk, e, he⟩ := hab
  obtain ⟨e2, he2⟩ := (hC k).1 e
  set b2 : Cochain (KA ⊞ KB) I n := pc biprod.fst a.1 + pc biprod.snd b0.1 with hb2def
  have hαb2 : pc (biprod.lift φ (-ψ)) b2 = pc φ a.1 - pc ψ b0.1 := by
    rw [hb2def, pc_add, ← pc_comp, ← pc_comp, biprod.lift_fst, biprod.lift_snd, pc_negm, sub_eq_add_neg]
  have hδb2 : δ n (n + 1) b2 = 0 := by
    rw [hb2def, δ_add, pc_δ, pc_δ, cocy_δ, cocy_δ, pc, pc, Cochain.comp_zero, Cochain.comp_zero, add_zero]
  have hr : pc (biprod.lift φ (-ψ)) (b - b2 - δ k n e2) = 0 := by
    have he2' : pc (biprod.lift φ (-ψ)) e2 = e := he2
    rw [pc_sub, pc_sub, ← pc_δ, he2', he]
    change _ - _ - (pc (biprod.lift φ (-ψ)) b - (pc φ a.1 - pc ψ b0.1)) = 0
    rw [hαb2]; abel
  obtain ⟨c3, hc3⟩ := (hC n).2.1 _ hr
  have hc3' : pc (biprod.desc u v) c3 = _ := hc3
  have hz : pc (biprod.desc u v) (δ n (n + 1) c3 - z.1) = 0 := by
    rw [pc_sub, ← pc_δ]
    change δ n (n + 1) (pc (biprod.desc u v) c3) - _ = 0
    rw [hc3', δ_sub, δ_sub, δ_δ, hδb2, hb]; simp
  have := (hC (n + 1)).2.2 _ hz
  exact (CohomologyClass.mk_eq_zero_iff _).2 ⟨n, rfl, c3, sub_eq_zero.1 this⟩

end LateralTheory.E.MVSpcPf

open LateralTheory.E.MVSpcPf in
theorem LateralTheory.E.MVPf.MVSpc_of (hS : Ses) : LateralTheory.E.MVPf.MVSpc := by
  intro _ R _ F U V E f g hc n hd x hxf hxg
  obtain ⟨w, hw⟩ := hS R f g hc
  have hI : ∀ k, Injective ((res R F).X k) := fun k => by unfold res; infer_instance
  exact chase hI _ _ _ _ w hw n hd x hxf hxg
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PrimMapComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.Deg0Pf

theorem exists_prim (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hA : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  obtain ⟨z, hz⟩ : ∃ z : S, (Polynomial.cyclotomic q S).eval z = 0 := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exact ⟨0, Subsingleton.elim _ _⟩
    · exact hA _ (Polynomial.cyclotomic.monic q S) (by
        rw [Polynomial.natDegree_cyclotomic]
        exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (ζ : Prim q A) : (ζ.map f).map g = ζ.map (g.comp f) := rfl

theorem rL_comp {S : Type} [CommRing S] (f g : S) :
    (rL f g).comp (algebraMap S (Localization.Away f)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_comp {S : Type} [CommRing S] (f g : S) :
    (rR f g).comp (algebraMap S (Localization.Away g)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem Deg0_of : LateralTheory.E.AcycQAPf.Deg0 := by
  intro hQ hH hL h9 q _ i S _ hS hq f g hfg c
  obtain ⟨e, he⟩ := hH h9 q i
  obtain ⟨ζ⟩ := exists_prim q S (hQ S hS).1 hq
  obtain ⟨a, b, hab⟩ := hL q S hS f g hfg ((e _ (ζ.map (algebraMap S (Localization.Away (f * g))))).symm c)
  refine ⟨e _ (ζ.map (algebraMap S (Localization.Away f))) a, e _ (ζ.map (algebraMap S (Localization.Away g))) b, ?_⟩
  rw [he, he, prim_map_comp, prim_map_comp, rL_comp, rR_comp, ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.Deg0Pf
end
end


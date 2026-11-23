module

public import Development.EtaleCohomology.EtaleSheaves.UliftSmulEq
public import Development.EtaleCohomology.EtaleSheaves.Bundle0059
public import Development.EtaleCohomology.EtaleSheaves.Bundle0058
public import Development.EtaleCohomology.EtaleSheaves.Bundle0060

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.RootPowPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.RootPowPf

theorem prim_eval {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : IsRoot (cyclotomic q A) ζ.1 := by
  have h := ζ.2.2
  rw [IsRoot.def, ← map_cyclotomic_int q A, Polynomial.eval_map]
  rw [aeval_def] at h
  exact h

theorem prim_pow {q : ℕ} {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := (prim_eval ζ).dvd (cyclotomic.dvd_X_pow_sub_one q A)
  simpa [IsRoot.def, sub_eq_zero] using h

theorem field_case {q : ℕ} {K : Type} [Field K] (ζ ξ : Prim q K) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  have : NeZero (q : K) := ⟨ζ.2.1.ne_zero⟩
  have : NeZero q := NeZero.of_neZero_natCast K
  have hζ : IsPrimitiveRoot ζ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ζ)
  have hξ : IsPrimitiveRoot ξ.1 q := isRoot_cyclotomic_iff.1 (prim_eval ξ)
  obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hξ.pow_eq_one
  have hc : i.Coprime q := (hζ.pow_iff_coprime (NeZero.pos q) i).1 (he ▸ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, he]

theorem local_case {q : ℕ} {O : Type} [CommRing O] [IsLocalRing O] (ζ ξ : Prim q O) :
    ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨a, ha⟩ := field_case (ζ.map (IsLocalRing.residue O)) (ξ.map (IsLocalRing.residue O))
  refine ⟨a, ?_⟩
  change IsLocalRing.residue O ξ.1 = (IsLocalRing.residue O ζ.1) ^ _ at ha
  rw [← map_pow] at ha
  set η := ζ.1 ^ (a : ZMod q).val with hη
  have hηq : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, prim_pow, one_pow]
  have hq : q ≠ 0 := by
    rintro rfl
    have := ζ.2.1
    simp at this
  have hηu : IsUnit η := IsUnit.of_pow_eq_one hηq hq
  have hg := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [prim_pow, hηq, sub_self] at hg
  have hu : IsUnit (∑ i ∈ Finset.range q, ξ.1 ^ i * η ^ (q - 1 - i)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, ha]
    rw [geom_sum₂_self]
    have h1 : IsUnit ((q : O) * η ^ (q - 1)) := ζ.2.1.mul (hηu.pow _)
    have h2 := (h1.map (IsLocalRing.residue O)).ne_zero
    simpa using h2
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 hg)

def sv {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : Sieve Y where
  arrows := fun Z g => ∃ a : (ZMod q)ˣ, (ξ.map g.appTop.hom).1 = (ζ.map g.appTop.hom).1 ^ (a : ZMod q).val
  downward_closed := by
    rintro Z W g ⟨a, ha⟩ h
    refine ⟨a, ?_⟩
    change g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ _ at ha
    change (h ≫ g).appTop.hom ξ.1 = (h ≫ g).appTop.hom ζ.1 ^ _
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, ha, map_pow]

theorem nhd {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ sv ζ ξ U.ι := by
  obtain ⟨a, ha⟩ := local_case (ζ.map (Y.presheaf.germ ⊤ y trivial).hom) (ξ.map (Y.presheaf.germ ⊤ y trivial).hom)
  change (Y.presheaf.germ ⊤ y trivial).hom ξ.1 = (Y.presheaf.germ ⊤ y trivial).hom ζ.1 ^ _ at ha
  rw [← map_pow] at ha
  obtain ⟨(U : Y.Opens), hU, i, i', he⟩ := TopCat.Presheaf.germ_eq Y.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ ha
  refine ⟨U, hU, a, ?_⟩
  change U.ι.appTop.hom ξ.1 = U.ι.appTop.hom ζ.1 ^ _
  rw [← map_pow]
  have hf : U.ι.appTop = Y.presheaf.map i.op ≫ U.topIso.inv := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact (Y.presheaf.map_comp _ _).symm ▸ rfl
  have hi : i' = i := Subsingleton.elim _ _
  subst hi
  rw [hf]
  exact congrArg U.topIso.inv.hom he

theorem sv_mem {q : ℕ} {Y : Scheme.{0}} (ζ ξ : Prim q Γ(Y, ⊤)) : sv ζ ξ ∈ Scheme.etaleTopology Y := by
  apply Scheme.zariskiTopology_le_etaleTopology
  choose U hU hS using nhd ζ ξ
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers Y (fun y => (U y : Scheme)) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hU y⟩, rfl⟩) (fun y => inferInstance), ?_⟩
  rintro _ _ ⟨y⟩
  exact hS y

theorem RootPow_of : LateralTheory.E.MulPf.RootPow := by
  classical
  intro q Y ζ s
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun _ _ _ ξ h => absurd h (Finset.notMem_empty ξ)⟩
  | insert ξ s _ ih =>
    obtain ⟨S, hS, h⟩ := ih
    refine ⟨S ⊓ sv ζ ξ, GrothendieckTopology.intersection_covering _ hS (sv_mem ζ ξ), ?_⟩
    rintro Z g ⟨h1, h2⟩ η hη
    rcases Finset.mem_insert.1 hη with rfl | hη
    · exact h2
    · exact h g h1 η hη

end LateralTheory.E.RootPowPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SimplicialPieceDiscrete
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.SimplicialPieceRelations SimplicialObject SimplicialObject.Augmented

namespace LateralTheory.E.SimplicialPieceDiscrete

variable (R : Type) [CommRing R]

def aug (X : PSh) : SimplicialObject.Augmented (Shv R) where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj X)
  right := (free R).obj X
  hom := { app := fun _ => 𝟙 _, naturality := by intros; (try simp); (try rfl) }

def augMap {X Y : PSh} (f : X ⟶ Y) : aug R X ⟶ aug R Y where
  left := ((SimplicialObject.whiskering _ _).obj (free R)).map (disc.map f)
  right := (free R).map f
  w := by
    apply NatTrans.ext; funext n; exact (Category.comp_id _).trans (Category.id_comp _).symm

def ed (X : PSh) : ExtraDegeneracy (aug R X) where
  s' := 𝟙 _
  s := fun _ => 𝟙 _
  s'_comp_ε := by simp [aug] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s₀_comp_δ₁ := by simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ₀ := by intro n; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_δ := by intro n i; simp [aug, SimplicialObject.δ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _
  s_comp_σ := by intro n i; simp [aug, SimplicialObject.σ] <;> first | rfl | exact Category.id_comp _ | exact Category.comp_id _

variable {R}

def hext {K L : ChainComplex (Shv R) ℕ} (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (by rw [HomologicalComplex.extendMap_comp])).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

def sIso (A : Shv R) := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat A 0 (0 : ℤ) (by simp)

theorem sIso_nat {A B : Shv R} (φ : A ⟶ B) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ (Shv R)).map φ) ComplexShape.embeddingDownNat ≫ (sIso B).hom =
      (sIso A).hom ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map φ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [sIso, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) (by simp),
    HomologicalComplex.single_map_f_self]
  erw [Iso.inv_hom_id_assoc]

theorem disc0 : Disc0 := by
  intro R _ X Y f
  refine ⟨HomotopyCategory.isoOfHomotopyEquiv (hext (ed R X).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _),
    HomotopyCategory.isoOfHomotopyEquiv (hext (ed R Y).homotopyEquiv) ≪≫ (Qt R).mapIso (sIso _), ?_⟩
  have hn := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := Shv R)).naturality (augMap R f)
  have key : (chains R).map (disc.map f) ≫ HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R Y)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj Y)).hom =
      HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ (sIso ((free R).obj X)).hom ≫
        (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := by
    have h2 := congrArg (fun φ => HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) hn
    simp only [HomologicalComplex.extendMap_comp] at h2
    have h1 : HomologicalComplex.extendMap ((point ⋙ ChainComplex.single₀ (Shv R)).map (augMap R f)) ComplexShape.embeddingDownNat ≫
        (sIso ((free R).obj Y)).hom = (sIso ((free R).obj X)).hom ≫
          (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f) := sIso_nat ((free R).map f)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (sIso ((free R).obj Y)).hom) h2).trans
      ((Category.assoc _ _ _).trans (congrArg (HomologicalComplex.extendMap (AlgebraicTopology.AlternatingFaceMapComplex.ε.app (aug R X)) ComplexShape.embeddingDownNat ≫ ·) h1)))
  have := congrArg (Qt R).map key
  simp only [Functor.map_comp] at this
  simp only [Iso.trans_hom, Category.assoc]
  exact this

theorem Piece_of : LateralTheory.E.TruncationPieces.Piece := LateralTheory.E.SimplicialPieceRelations.piece_of disc0

end LateralTheory.E.SimplicialPieceDiscrete
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SysFMPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.SysFMPf

def phi {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Γ(w.normalization, ⊤) →+* W :=
  (w.toNormalization.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom

def RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) : Set w.normalization :=
  {y | ∀ s : Γ(w.normalization, ⊤), IsIdempotentElem (phi w s) → phi w s ∉ q.asIdeal → y ∈ w.normalization.basicOpen s}

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ⋂ j, Set.range (ι j) = RR w q

def FMex : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m ∧
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization ∧
      Mono m ∧ Flat m ∧ QuasiCompact m

def FMrange : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ (q : PrimeSpectrum W)
    (m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization),
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m →
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization →
      Set.range m = RR w q

theorem SysFM_of (hS : Sys) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hS W w hW y
  obtain ⟨m, e1, e2, hm, hf, hq⟩ := hE W w hW q
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, m, hm, hf, hq, ?_⟩
  rw [h3]
  exact hR W w hW q m e1 e2

end LateralTheory.E.SysFMPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TruncBijPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncBijPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {K K' L : CochainComplex C ℤ}

def preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) : Cochain K L j := (Cochain.ofHom g).comp z (zero_add j)

theorem preC_v (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (p q : ℤ) (h : p + j = q) :
    (preC g z).v p q h = g.f p ≫ z.v p q h := by
  simp [preC]

theorem δ_preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (k : ℤ) : δ j k (preC g z) = preC g (δ j k z) :=
  δ_ofHom_comp g z k

theorem preC_zero (g : K ⟶ K') (j : ℤ) : preC g (0 : Cochain K' L j) = 0 := by
  simp [preC]

theorem preC_inj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) {x y : Cochain K' L j}
    (h : preC g x = preC g y) : x = y := by
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have := hg p (by omega)
    have h' := congrArg (fun z : Cochain K L j => z.v p q hpq) h
    simp only [preC_v] at h'
    exact (cancel_epi (g.f p)).1 h'

theorem preC_surj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) (y : Cochain K L j) :
    ∃ x : Cochain K' L j, preC g x = y := by
  refine ⟨Cochain.mk fun p q hpq =>
    if h : -(n + 1) ≤ p then (haveI := hg p h; inv (g.f p)) ≫ y.v p q hpq else 0, ?_⟩
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have hp : -(n + 1) ≤ p := by omega
    rw [preC_v, Cochain.mk_v, dite_eq_left hp, IsIso.hom_inv_id_assoc]

end General

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) :=
  CochainComplex.isZero_of_isStrictlyGE (injectiveResolution F).cochainComplex 0 q hq

theorem pull_mk (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (m : ℤ) (x : Cocycle K' (res R F) m) :
    ∃ y : Cocycle K (res R F) m, HK.pull R g F m (CohomologyClass.mk x) = CohomologyClass.mk y ∧
      (y : Cochain K (res R F) m) = preC g (x : Cochain K' (res R F) m) :=
  ⟨_, rfl, rfl⟩

end LateralTheory.E.TruncBijPf

open LateralTheory.E.TruncBijPf in
theorem LateralTheory.E.TruncPf.TruncBij_of : LateralTheory.E.TruncPf.TruncBij := by
  intro R _ F K K' g n hg m hm
  have hL := res_isZero R F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, hy, hy'⟩ := pull_mk R F g m x
    rw [hy, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := preC_surj g n hg hL (by omega) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
    refine ⟨β', preC_inj g n hg hL (by omega) ?_⟩
    rw [← δ_preC, hβ, hy']
  · intro y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, hx⟩ := preC_surj g n hg hL (j := m) (by omega) (y : Cochain K (res R F) m)
    have hδ : δ m (m + 1) x = 0 := by
      apply preC_inj g n hg hL (by omega)
      rw [← δ_preC, hx, preC_zero, Cocycle.δ_eq_zero]
    obtain ⟨y', hy, hy'⟩ := pull_mk R F g m (Cocycle.mk x (m + 1) rfl hδ)
    refine ⟨_, hy.trans (congrArg CohomologyClass.mk (Cocycle.ext ?_))⟩
    rw [hy', ← hx]
    rfl
end
end


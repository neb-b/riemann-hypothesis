module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0025
public import Development.EtaleCohomology.EtaleSheaves.Bundle0026
public import Development.EtaleCohomology.EtaleSheaves.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LChartPf
section
noncomputable section

namespace LateralTheory.E.LChartPf

def IdemLiftInt (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def LIdemLift : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IdemLiftInt A I

def LSurjChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem isStandardEtale_of_surjective (A : Type) [CommRing A] (A' : Type) [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (g : A') (hs : Function.Surjective (algebraMap A (Localization.Away g))) :
    Algebra.IsStandardEtale A (Localization.Away g) :=
  Algebra.IsStandardEtale.of_surjective (S := A) (Algebra.ofId A _) hs

theorem LChart_of (h1 : LIdemLift) (h2 : LSurjChart) : LateralTheory.E.LEtaleLiftPf.LChart := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hs⟩ := h2 A I (by simpa only [Ideal.jacobson_bot] using
    (HenselianRing.jac : I ≤ Ring.jacobson A)) (h1 A I) A' φ
  exact ⟨g, hg, isStandardEtale_of_surjective A A' g hs⟩

end LateralTheory.E.LChartPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_prim_locPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

section Alg
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A]

theorem prim_pow_q (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  have h := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (Polynomial.aeval ζ.1) hr
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h2
  exact sub_eq_zero.1 h2

theorem prim_isPrim {B : Type} [CommRing B] [IsDomain B] (φ : A →+* B) (ζ : Prim q A) :
    IsPrimitiveRoot (φ ζ.1) q := by
  have hq : IsUnit (q : B) := by simpa using ζ.2.1.map φ
  haveI : NeZero (q : B) := ⟨hq.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := (Prim.map φ ζ).2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact h

theorem unit_sub (ζ : Prim q A) {j : ℕ} (hj0 : 0 < j) (hjq : j < q) : IsUnit (ζ.1 ^ j - 1) := by
  by_contra h
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
  have hp := prim_isPrim (Ideal.Quotient.mk m) ζ
  have h0 : Ideal.Quotient.mk m (ζ.1 ^ j - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
  rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
  exact hp.pow_ne_one_of_pos_of_lt (Nat.pos_iff_ne_zero.1 hj0) hjq h0

end Alg

section Idem
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (x : A)

def yy (a : ℕ) : A := x * ζ.1 ^ (a * (q - 1))
def ee (a : ℕ) : A := (ζ.2.1.unit⁻¹ : Aˣ) * ∑ j ∈ Finset.range q, (yy ζ x a) ^ j

theorem zeta_mul_yy (a : ℕ) : ζ.1 ^ a * yy ζ x a = x := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  unfold yy
  rw [show q - 1 = k by omega]
  calc ζ.1 ^ a * (x * ζ.1 ^ (a * k)) = x * ζ.1 ^ (a + a * k) := by rw [pow_add]; ring
    _ = x * (ζ.1 ^ (k + 1)) ^ a := by rw [← pow_mul]; ring_nf
    _ = x := by rw [hz, one_pow, mul_one]

theorem ee_kill (hx : x ^ q = 1) (a : ℕ) : ee ζ x a * (x - ζ.1 ^ a) = 0 := by
  have h1 : x - ζ.1 ^ a = ζ.1 ^ a * (yy ζ x a - 1) := by
    rw [mul_sub, zeta_mul_yy, mul_one]
  have hy : (yy ζ x a) ^ q = 1 := by
    unfold yy
    rw [mul_pow, hx, ← pow_mul, mul_comm (a * (q - 1)) q, pow_mul, prim_pow_q, one_pow, one_mul]
  unfold ee
  rw [h1]
  calc _ = ((ζ.2.1.unit⁻¹ : Aˣ) : A) * ζ.1 ^ a * ((∑ j ∈ Finset.range q, (yy ζ x a) ^ j) * (yy ζ x a - 1)) := by ring
    _ = 0 := by rw [geom_sum_mul, hy, sub_self, mul_zero]

theorem inner_sum {j : ℕ} (hj0 : 0 < j) (hjq : j < q) :
    ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hz : ζ.1 ^ (k + 1) = 1 := by rw [show k + 1 = q by omega]; exact prim_pow_q ζ
  have hik : i < k := by omega
  have e1 : (q - 1) * (i + 1) = (k + 1) * i + (k - i) := by
    rw [show q - 1 = k by omega]; zify [hik.le]; ring
  have hw : ζ.1 ^ ((q - 1) * (i + 1)) = ζ.1 ^ (k - i) := by
    rw [e1, pow_add, pow_mul, hz, one_pow, one_mul]
  have hu : IsUnit (ζ.1 ^ (k - i) - 1) := unit_sub ζ (by omega) (by omega)
  have hwq : (ζ.1 ^ (k - i)) ^ q = 1 := by rw [← pow_mul, mul_comm, pow_mul, prim_pow_q, one_pow]
  rw [hw]
  have h2 := geom_sum_mul (ζ.1 ^ (k - i)) q
  rw [hwq, sub_self] at h2
  exact (hu.mul_left_eq_zero).1 h2

theorem ee_sum : ∑ a ∈ Finset.range q, ee ζ x a = 1 := by
  unfold ee yy
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range q, ∑ a ∈ Finset.range q, (x * ζ.1 ^ (a * (q - 1))) ^ j =
      x ^ j * ∑ a ∈ Finset.range q, (ζ.1 ^ ((q - 1) * j)) ^ a := by
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [inner_sum ζ (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne q))) h

end Idem

theorem ee_nil {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : ℕ) (ha : ¬ a.Coprime q) :
    IsNilpotent (ee ζ ξ.1 a) := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  intro p hp
  haveI : Ideal.IsPrime p := hp
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  by_contra hne
  have hk := congrArg (Ideal.Quotient.mk p) (ee_kill ζ ξ.1 (prim_pow_q ξ) a)
  rw [map_mul, map_zero, map_sub, map_pow] at hk
  have he : Ideal.Quotient.mk p ξ.1 = (Ideal.Quotient.mk p ζ.1) ^ a :=
    sub_eq_zero.1 ((mul_eq_zero.1 hk).resolve_left hne)
  have hξ := prim_isPrim (Ideal.Quotient.mk p) ξ
  have hζ := prim_isPrim (Ideal.Quotient.mk p) ζ
  rw [he] at hξ
  exact ha ((hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 hξ)

theorem algPow : AlgPow := by
  intro q _ A _ ζ ξ
  refine ⟨Set.range fun a : Fin q => ee ζ ξ.1 a, ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← ee_sum ζ ξ.1, Finset.sum_range]
    exact Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨a, rfl⟩
  · rintro f ⟨a, rfl⟩
    by_cases hc : (a : ℕ).Coprime q
    · refine ⟨ZMod.unitOfCoprime a hc, 1, ?_⟩
      have hv : ((ZMod.unitOfCoprime (a : ℕ) hc : (ZMod q)ˣ) : ZMod q).val = a := by
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt a.2]
      rw [hv, pow_one]
      exact ee_kill ζ ξ.1 (prim_pow_q ξ) a
    · obtain ⟨n, hn⟩ := ee_nil ζ ξ a hc
      exact ⟨1, n, by rw [hn, zero_mul]⟩

theorem loc_of_span {U : Scheme.{0}} (s : Set Γ(U, ⊤)) (hs : Ideal.span s = ⊤) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ f ∈ s, ∀ (V : Scheme.{0}) (g : V ⟶ U), IsUnit (g.appTop.hom f) → P V g) : Loc U P := by
  let O : s → U.Opens := fun f => U.basicOpen f.1
  have hO : TopologicalSpace.IsOpenCover O := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, U.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := U.openCoverOfIsOpenCover O hO
  let S : Sieve U := {
    arrows := fun V g => ∃ f ∈ s, IsUnit (g.appTop.hom f)
    downward_closed := by
      rintro V W g ⟨f, hf, hu⟩ k
      exact ⟨f, hf, (show IsUnit (k.appTop.hom (g.appTop.hom f)) from hu.map _)⟩ }
  have hgen : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ≤ S := by
    rintro W g ⟨Y, k, _, ⟨i⟩, rfl⟩
    refine (S.downward_closed ?_ k)
    refine ⟨i.1, i.2, ?_⟩
    have hle : (O i).ι ''ᵁ ⊤ ≤ U.basicOpen i.1 := by simp [O]
    have := (U.toRingedSpace.isUnit_res_basicOpen i.1).map (U.presheaf.map (homOfLE hle).op).hom
    have e : U.presheaf.map (homOfLE (x := (O i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        U.presheaf.map (homOfLE (U.basicOpen_le i.1)).op ≫ U.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    show IsUnit ((O i).ι.appTop.hom i.1)
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  refine ⟨S, Scheme.etaleTopology.superset_covering hgen
    (Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩)), ?_⟩
  rintro V g ⟨f, hf, hu⟩
  exact h f hf V g hu

theorem eq_of_unit_kill {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) {f x y : A} {n : ℕ}
    (hn : f ^ n * (x - y) = 0) (hu : IsUnit (φ f)) : φ x = φ y := by
  have h0 : φ (f ^ n * (x - y)) = 0 := by rw [hn, map_zero]
  rw [map_mul, map_pow, map_sub] at h0
  exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)

theorem loc_mono' {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem c2 (hA : AlgPow) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) :
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val := by
  obtain ⟨s, hs, hf⟩ := hA q Γ(U, ⊤) ζ ξ
  refine loc_of_span s hs fun f hfs V g hu => ?_
  obtain ⟨a, n, hn⟩ := hf f hfs
  exact ⟨a, by rw [eq_of_unit_kill g.appTop.hom hn hu, map_pow]⟩

end LateralTheory.E.L_prim_locPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LSchClsPfYon
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sch_clsPfYon

variable (R : Type) [CommRing R]

def yon0 (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (freeP R).obj (yoneda.obj X) ⟶ G.obj where
  app U := ModuleCat.freeDesc (R := ULift.{1} R) (X := ULift.{1} (U.unop ⟶ X)) (TypeCat.ofHom (fun g : ULift.{1} (U.unop ⟶ X) => (G.obj.map g.down.op).hom z))
  naturality U V f := by
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    have e1 : (((freeP R).obj (yoneda.obj X)).map f).hom (ModuleCat.freeMk (ULift.up g)) =
        ModuleCat.freeMk (ULift.up (f.unop ≫ g)) := ModuleCat.free_map_apply (R := ULift.{1} R) _ _
    erw [ConcreteCategory.comp_apply, e1, ConcreteCategory.comp_apply, ModuleCat.freeDesc_apply]
    erw [ModuleCat.freeDesc_apply]
    show (G.obj.map (f.unop ≫ g).op).hom z = (G.obj.map f).hom ((G.obj.map g.op).hom z)
    rw [op_comp, Functor.map_comp]
    rfl

def yon (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : (free R).obj (yoneda.obj X) ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.property⟩

theorem yon_gen (G : Shv R) (X : Scheme.{0}) (z : Sec G X) : Sec.map (yon R G X z) (freeGen R _ X (𝟙 X)) = z := by
  have h := toSheafify_sheafifyLift Scheme.etaleTopology (yon0 R G X z) G.property
  have := congrArg (fun φ => (φ.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) h
  refine this.trans ?_
  dsimp only [yon0]
  erw [ModuleCat.freeDesc_apply]
  simp

theorem yon_ext {G : Shv R} {X : Scheme.{0}} (φ ψ : (free R).obj (yoneda.obj X) ⟶ G)
    (h : Sec.map φ (freeGen R _ X (𝟙 X)) = Sec.map ψ (freeGen R _ X (𝟙 X))) : φ = ψ := by
  have key : ∀ (U : Scheme.{0}) (g : U ⟶ X), Sec.map φ (freeGen R _ U g) = Sec.map ψ (freeGen R _ U g) := by
    intro U g
    have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
      rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
      simp
    rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, h]
  have hv : φ.hom = ψ.hom := by
    apply sheafify_hom_ext Scheme.etaleTopology _ _ G.property
    refine NatTrans.ext (funext fun U => ?_)
    apply ModuleCat.free_hom_ext (R := ULift.{1} R)
    rintro ⟨g⟩
    exact key U.unop g
  first | exact Sheaf.hom_ext hv | (cases φ; cases ψ; cases hv; rfl)

theorem yon_res {G : Shv R} {X : Scheme.{0}} (z : Sec G X) (U : Scheme.{0}) (g : U ⟶ X) :
    Sec.map (yon R G X z) (freeGen R _ U g) = Sec.res g z := by
  have hg : freeGen R (yoneda.obj X) U g = Sec.res g (freeGen R _ X (𝟙 X)) := by
    rw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
    simp
  rw [hg, ← LateralTheory.E.LeafKumSpecPf.sec_res_map, yon_gen]

end LateralTheory.E.L_sch_clsPfYon
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LZHensFinitePf

def HensIdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
  (e : B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)), IsIdempotentElem e →
  ∃ f : B, IsIdempotentElem f ∧ Ideal.Quotient.mk _ f = e

theorem hensIdemLift : HensIdemLift := by
  intro A _ _ _ B _ _ _ e he
  exact GlobalTheory.exists_idempotent_lift_of_henselian A (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective he

theorem idem_triv_of_preconnected (R : Type) [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
    (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply he.eq_zero_of_isNilpotent
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact SetLike.coe_injective h
  · right
    have hz : PrimeSpectrum.zeroLocus ({e} : Set R) = ∅ := by
      rw [← compl_compl (PrimeSpectrum.zeroLocus ({e} : Set R)), ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h,
        Set.compl_univ]
    have h1 : IsNilpotent (1 - e) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply SetLike.coe_injective
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel, hz]
      rfl
    exact (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent h1)).symm

theorem subsingleton_of_idem (R : Type) [CommRing R] [IsArtinianRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum R) := by
  have hp : PreconnectedSpace (PrimeSpectrum R) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left; simp
    · right; simp
  exact ⟨fun x y => hp.constant (f := id) continuous_id⟩

theorem LZHensFinite_of_lift (hL : HensIdemLift) : LateralTheory.E.LZProperCut.LZHensFinite := by
  intro A _ _ _ B _ _ _ hB
  have : ConnectedSpace (PrimeSpectrum B) := hB
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  set I := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hI
  have hle : ∀ M : Ideal B, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    have : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  have htriv : ∀ e : B ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := hL A B e he
    rcases idem_triv_of_preconnected B f hf with rfl | rfl
    · left; simp
    · right; simp
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I)
  have hsub := subsingleton_of_idem (B ⧸ I) htriv
  have key : ∀ P : Ideal B, P.IsMaximal →
      P = (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) ∧ (P.map (Ideal.Quotient.mk I)).IsPrime := by
    intro P hP
    refine ⟨(Ideal.comap_map_mk (hle P hP)).symm, ?_⟩
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle P hP)
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  refine ⟨M, hM, fun N hN => ?_⟩
  obtain ⟨hN1, hN2⟩ := key N hN
  obtain ⟨hM1, hM2⟩ := key M hM
  have : (⟨_, hN2⟩ : PrimeSpectrum (B ⧸ I)) = ⟨_, hM2⟩ := Subsingleton.elim _ _
  exact hN1.trans ((congrArg (fun P : PrimeSpectrum (B ⧸ I) => P.asIdeal.comap (Ideal.Quotient.mk I)) this).trans hM1.symm)

end LateralTheory.E.LZHensFinitePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafCurveVCut

def LeafFibreField : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (F : Type) (_ : Field F) (_ : Algebra k F) (K : Type) (_ : Field K) (_ : Algebra F K)
    (n : ℕ) (s : Finset F) (t : K) (η : Sp K ⟶ X), (n : WithBot ℕ∞) < topologicalKrullDim X ∧ s.card ≤ n ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
    FiniteDimensional (IntermediateField.adjoin F {t}) K ∧
    η ≫ p = Spec.map (CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F))) ∧ genericPoint X ∈ Set.range η

def LeafTrdegDim : Prop := ∀ (k F Ω : Type) [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] [Algebra.IsAlgebraic F Ω] (n : ℕ) (s : Finset F), s.card ≤ n →
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F →
    ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R ≤ n

def LeafBaseChangeField : Prop := ∀ (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra F K] (t : K),
  Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K →
    ∃ (L : Type) (_ : Field L) (_ : Algebra Ω L) (u : L) (φ : K →+* L), Transcendental Ω u ∧
      FiniteDimensional (IntermediateField.adjoin Ω {u}) L ∧ φ.comp (algebraMap F K) = (algebraMap Ω L).comp (algebraMap F Ω)

def LeafModelCurve : Prop := ∀ (Ω L : Type) [Field Ω] [IsAlgClosed Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L), IsCurve c0 ∧
      IsGenericPoint x (⊤ : Set C0) ∧ ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafExtend : Prop := ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] {X C0 : Scheme.{0}} (p : X ⟶ Sp k)
  [IsProper p] (c0 : C0 ⟶ Sp Ω) (x : C0), IsCurve c0 → IsGenericPoint x (⊤ : Set C0) →
    ∀ ψ : Spec (C0.presheaf.stalk x) ⟶ X,
      ψ ≫ p = C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
      ∃ e : C0 ⟶ X, C0.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))

theorem goal_of (hA : LeafFibreField) (hT : LeafTrdegDim) (hB1 : LeafBaseChangeField) (hB2 : LeafModelCurve)
    (hC : LeafExtend) : LateralTheory.E.LeafGeoVCut.LeafCurveV := by
  intro k _ _ X _ p _ hd
  obtain ⟨F, _, _, K, _, _, n, s, t, η, hn, hs, halg, ht, hfin, hη, hgen⟩ := hA k p hd
  obtain ⟨L, _, _, u, φ, hu, hufin, hφ⟩ := hB1 F (AlgebraicClosure F) K t ht hfin
  obtain ⟨C0, c0, x, ψ, hc0, hx, hψ⟩ := hB2 (AlgebraicClosure F) L u hu hufin
  have hring : CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F)) ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap k (AlgebraicClosure F)) ≫ CommRingCat.ofHom (algebraMap (AlgebraicClosure F) L) := by
    ext a
    have := congrArg (fun f => f (algebraMap k F a)) hφ
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, this,
      IsScalarTower.algebraMap_apply k F (AlgebraicClosure F)]
  have hcompat : (ψ ≫ Spec.map (CommRingCat.ofHom φ) ≫ η) ≫ p =
      C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure F))) := by
    rw [Category.assoc, Category.assoc, hη, ← Spec.map_comp, hring, Spec.map_comp, ← Category.assoc, hψ,
      Category.assoc]
  obtain ⟨e, he1, he2⟩ := hC k (AlgebraicClosure F) p c0 x hc0 hx _ hcompat
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, C0, c0, e, hc0, he2, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hgen
    let w : Spec (C0.presheaf.stalk x) := IsLocalRing.closedPoint (C0.presheaf.stalk x)
    refine ⟨C0.fromSpecStalk x w, ?_⟩
    rw [← Scheme.Hom.comp_apply, he1, ← hz]
    simp only [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  · intro R hR
    exact lt_of_le_of_lt (hT k F (AlgebraicClosure F) n s hs halg R hR) hn

end LateralTheory.E.LeafCurveVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocPf

def overIso {R : Type} [CommRing R] (X : Scheme.{0}) (F G : Shv R)
    (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U))
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) :
    F.over X ≅ G.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun Y => (e Y.unop.left Y.unop.hom).toModuleIso) (by
    intro Y Y' f
    ext s
    have h := he f.unop.left Y.unop.hom s
    rw [Over.w f.unop] at h
    exact h))

def LocOver : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

theorem LeafLoc_of (hO : LocOver) : LateralTheory.E.LeafTwistPf.LeafLoc := by
  intro hy R _ X F G e he n
  exact hO hy R X F G ⟨overIso X F G e he⟩ n

abbrev secCx {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) : CochainComplex (ModuleCat.{1} (ULift.{1} R)) ℤ :=
  ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)).mapHomologicalComplex _).obj (res R F)

def LocSec : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ (secCx F X).homology n)

def LocSlice : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty ((secCx F X).homology n ≃+ (secCx G X).homology n)

theorem LocOver_of (hS : LocSec) (hL : LocSlice) : LocOver := by
  intro hy R _ X F G hi n
  obtain ⟨a⟩ := hS hy R X F n
  obtain ⟨b⟩ := hS hy R X G n
  obtain ⟨c⟩ := hL hy R X F G hi n
  exact ⟨(a.trans c).trans b.symm⟩

theorem LeafLoc_of' (hS : LocSec) (hL : LocSlice) : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LeafLoc_of (LocOver_of hS hL)

end LateralTheory.E.LeafLocPf
end
end


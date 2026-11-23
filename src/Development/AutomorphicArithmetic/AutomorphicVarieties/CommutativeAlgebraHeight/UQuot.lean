module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

namespace UpperTheory.V.CA

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

noncomputable def coord (D : GDet n A G) (t : ℕ × G) : A := D.lam t.1 (MonoidAlgebra.single t.2 1)

theorem coord_ext {D D' : GDet n A G} (h : ∀ t, coord D t = coord D' t) : D = D' := by
  have hlam (E : GDet n A G) (i : ℕ) (y : MonoidAlgebra A G) :
      E.toDet.lam i y = E.lam i y := by
    suffices hchi : E.toDet.chi y = E.chi y by simp only [Det.lam, GDet.lam, hchi]
    change E.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      E.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  have hdet : D.toDet = D'.toDet := by
    refine d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [eq_top_iff]
      rintro x -
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i _ _
      rw [hlam, hlam]
      exact h (i, g)
  rw [← GDet.ofDet_toDet D, hdet, GDet.ofDet_toDet]

theorem coord_map (D : GDet n A G) {B : Type} [CommRing B] (f : A →+* B) (t : ℕ × G) :
    coord (D.map f) t = f (coord D t) := by
  have hchi : (D.map f).chi (MonoidAlgebra.single t.2 1) =
      (D.chi (MonoidAlgebra.single t.2 1)).map f := by
    let : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
    let φ : A[X] →ₐ[A] B[X] :=
      { Polynomial.mapRingHom f with
        commutes' := fun a => by
          change Polynomial.map f (C a) = C (f a)
          exact Polynomial.map_C f }
    refine Eq.trans ?_ (D.nat A[X] B[X] φ
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single t.2 1)))
    change D.D B[X] _ = D.D B[X] _
    congr 1
    have hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f := rfl
    rw [hφ]
    simp
  simp only [coord, GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

theorem coord_comap (D : GDet n A G) {H : Type} [Group H] (φ : H →* G) (t : ℕ × H) :
    coord (D.comap φ) t = coord D (t.1, φ t.2) := by
  unfold coord GDet.lam GDet.chi
  congr 2
  change (D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _)).coeff = (D.D A[X] _).coeff
  congr 1
  rw [map_sub]
  simp

theorem exists_comap_quot (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ h ∈ H, D.Kills (MonoidAlgebra.single h 1 - 1)) :
    ∃ D0 : GDet n A (G ⧸ H), D0.comap (QuotientGroup.mk' H) = D := by
  have hk : ∀ h ∈ H, (MonoidAlgebra.single h 1 - 1 : MonoidAlgebra A G) ∈ D.toDet.ker := by
    intro h hh
    apply (d_ker D.toDet _).1.2
    intro S _ _ y
    change D.D S (ofT A G S (1 + y * (1 ⊗ₜ (MonoidAlgebra.single h 1 - 1)))) = 1
    rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
    exact hD h hh S _
  let f : MonoidAlgebra A G →ₐ[A] MonoidAlgebra A (G ⧸ H) := MonoidAlgebra.mapDomainAlgHom A A (QuotientGroup.mk' H)
  let σ : MonoidAlgebra A (G ⧸ H) →+ MonoidAlgebra A G :=
    { toFun := MonoidAlgebra.mapDomain Quotient.out
      map_zero' := MonoidAlgebra.mapDomain_zero _
      map_add' := MonoidAlgebra.mapDomain_add _ }
  have h1 : ∀ y, f (σ y) = y := fun y => by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [f, σ]
  have h2 : ∀ x, x - σ (f x) ∈ D.toDet.ker := fun x => by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact D.toDet.ker.add_mem ha hb
    | single g r =>
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
      have : MonoidAlgebra.single g r - σ (f (MonoidAlgebra.single g r)) =
          - (MonoidAlgebra.single g r * (MonoidAlgebra.single (h : G) 1 - 1)) := by
        simp [f, σ, hh, mul_sub, MonoidAlgebra.single_mul_single]
      rw [this]
      exact D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hk h h.2))
  obtain ⟨D', hD', -⟩ := d_factor D.toDet f (fun y => ⟨_, h1 y⟩) fun x hx => by
    simpa [hx] using h2 x
  refine ⟨GDet.ofDet D', GDet.ext fun S _ _ x => ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  change D'.D S (toT A _ S (MonoidAlgebra.mapDomainRingHom S (QuotientGroup.mk' H) x)) =
    D'.D S (Algebra.TensorProduct.map (AlgHom.id S S) f (toT A G S x))
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [f, toT_single]

theorem exists_comap_level [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (D : GDet n A G) (I : Ideal A) (hc : D.IsCont I) {N : ℕ} (hN : I ^ N = ⊥) :
    ∃ H : OpenNormalSubgroup G, ∀ (K : Subgroup G) [K.Normal], K ≤ H.toSubgroup →
      ∃ D0 : GDet n A (G ⧸ K), D0.comap (QuotientGroup.mk' K) = D := by
  have locallyInvariant {X : Type} {f : G → X} (hf : IsLocallyConstant f) :
      ∀ᶠ h in nhds (1 : G), ∀ g, f (g * h) = f g := by
    have hfiber : ∀ y ∈ Set.range f, ∀ᶠ h in nhds (1 : G), ∀ g, f g = y → f (g * h) = y := by
      intro y _
      obtain ⟨T, hT, hW⟩ := IsTopologicalGroup.exist_mul_closure_nhds (hf.isClopen_fiber y)
      filter_upwards [hT] with h hh g hg
      exact hW (Set.mul_mem_mul (show g ∈ {x | f x = y} from hg) hh)
    filter_upwards [(Filter.eventually_all_finite hf.range_finite).2 hfiber] with h hh g
    exact hh _ ⟨g, rfl⟩ g rfl
  have hlocal := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun i _ =>
    locallyInvariant (hc i N)
  obtain ⟨U, hU, hUo, hU1⟩ := mem_nhds_iff.1 hlocal
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  have hcoeff (i : ℕ) (hi : i ≤ n) (h : G) (hh : h ∈ H) (g : G) :
      D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1) := by
    have heq := hU (hH hh) i hi g
    exact sub_eq_zero.mp (by simpa [hN] using Ideal.Quotient.eq.1 heq)
  have hlam (i : ℕ) (y : MonoidAlgebra A G) : D.toDet.lam i y = D.lam i y := by
    suffices hchi : D.toDet.chi y = D.chi y by simp only [Det.lam, GDet.lam, hchi]
    change D.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  have hfinite {k : ℕ} (g g' : Fin k → G) (hg : ∀ a, (g a : G ⧸ H.toSubgroup) = g' a)
      (S : Type) [CommRing S] [Algebra A S] (s : Fin k → S) :
      D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) =
        D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
    have lift_single (w : FreeMonoid (Fin k)) (b : Fin k → G) :
        FreeMonoid.lift (fun a => (MonoidAlgebra.single (b a) 1 : MonoidAlgebra A G)) w =
          MonoidAlgebra.single (FreeMonoid.lift b w) 1 := by
      induction w using FreeMonoid.inductionOn' with
      | one => simp [MonoidAlgebra.one_def]
      | of_mul a w ih => simp [ih, MonoidAlgebra.single_mul_single]
    have lift_quot (w : FreeMonoid (Fin k)) :
        ((FreeMonoid.lift g w : G) : G ⧸ H.toSubgroup) = FreeMonoid.lift g' w := by
      induction w using FreeMonoid.inductionOn' with
      | one => simp
      | of_mul a w ih => simp [ih, hg]
    have heval (b : Fin k → G) :
        D.D S (1 + ∑ a, MonoidAlgebra.single (b a) (s a)) =
          MvPolynomial.aeval s (D.toDet.D (MvPolynomial (Fin k) A)
            (1 + Det.gen fun a => (MonoidAlgebra.single (b a) 1 : MonoidAlgebra A G))) := by
      rw [← D.toDet.nat]
      change _ = D.D S (ofT A G S _)
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Det.gen, map_sum, ofT_tmul]
    rw [heval, heval]
    congr 1
    ext α
    obtain ⟨P, hP, -, hP'⟩ := d_amitsur n k α
    rw [hP', hP']
    refine MvPolynomial.hom_congr_vars ?_ ?_ rfl
    · ext a
      simp
    · intro v hv _
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, lift_single, hlam]
      have hv' := QuotientGroup.eq.1 (lift_quot v.2)
      rw [← hcoeff v.1 (hP v hv).2.1 _ hv', mul_inv_cancel_left]
  have hsum {ι : Type} [Fintype ι] (g g' : ι → G) (hg : ∀ a, (g a : G ⧸ H.toSubgroup) = g' a)
      (S : Type) [CommRing S] [Algebra A S] (s : ι → S) :
      D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) =
        D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
    let e := (Fintype.equivFin ι).symm
    rw [← e.sum_comp, ← e.sum_comp (fun a => MonoidAlgebra.single (g' a) (s a))]
    exact hfinite (g ∘ e) (g' ∘ e) (fun a => hg _) S (s ∘ e)
  have hkills (h : G) (hh : h ∈ H) : D.Kills (MonoidAlgebra.single h 1 - 1) := by
    intro S _ _ u
    have hu : ∃ (ι : Type) (_ : Fintype ι) (g : ι → G) (s : ι → S),
        u = ∑ a, MonoidAlgebra.single (g a) (s a) := by
      induction u using MonoidAlgebra.induction_linear with
      | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, by simp⟩
      | single g r => exact ⟨Unit, inferInstance, fun _ => g, fun _ => r, by simp⟩
      | add a b ha hb =>
        obtain ⟨ι, _, g, s, rfl⟩ := ha
        obtain ⟨ι', _, g', s', rfl⟩ := hb
        exact ⟨ι ⊕ ι', inferInstance, Sum.elim g g', Sum.elim s s', by simp⟩
    obtain ⟨ι, _, g, s, rfl⟩ := hu
    have hcancel := hsum (ι := ι ⊕ ι) (Sum.elim (fun a => g a * h) g) (Sum.elim g g)
      (by rintro (a | a)
          · simpa using (show h ∈ H.toOpenSubgroup from hh)
          · rfl) S (Sum.elim s fun a => -s a)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, MonoidAlgebra.single_neg,
      Finset.sum_neg_distrib, add_neg_cancel, add_zero, map_one] at hcancel
    rw [← hcancel]
    congr 2
    simp [Finset.sum_mul, MonoidAlgebra.single_mul_single, sub_eq_add_neg, mul_add]
  exact ⟨H, fun K _ hK => exists_comap_quot D K fun h hh => hkills h (hK hh)⟩

end UpperTheory.V.CA

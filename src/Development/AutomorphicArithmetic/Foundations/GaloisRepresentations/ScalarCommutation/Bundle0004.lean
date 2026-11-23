module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0126

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CnjApply
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp cj lev GLw mat)
open UpperTheory.Gal.LocalSmoothExtension UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private def cnj {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k where
  toFun x := (a⁻¹).val * x * a.val
  map_one' := by simp
  map_mul' x y := by
    have h : a.val * (a⁻¹).val = 1 := Units.mul_inv a
    calc (a⁻¹).val * (x * y) * a.val = (a⁻¹).val * x * 1 * y * a.val := by simp [Matrix.mul_assoc]
      _ = _ := by rw [← h]; simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

private def rd (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) : AfP p ⊗[ℚ] E →+* w.adicCompletion E :=
  RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, fun x hx => by
    have := (T.Φ_ker x).1 hx w hp
    exact this⟩

private theorem rd_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : Af E) : rd T w hp (T.Φ x) = pLoc E w x :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

private def aw (T : Tr S) (w : Plc E) : GL (Fin n) (w.adicCompletion E) := GeneralLinearGroup.map (pLoc E w) T.a

private theorem cnj_apply {k : Type} [Field k] {n : ℕ} (a : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) :
    cnj a x = (a⁻¹).val * x * a.val := rfl

private theorem alg_mat (n : ℕ) (w : Plc E) (r : E) :
    (algebraMap E (Matrix (Fin n) (Fin n) E) r).map (algebraMap E (w.adicCompletion E)) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.algebraMap_matrix_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

private theorem cnj_alg {w : Plc E} (a : GL (Fin n) (w.adicCompletion E)) (r : E) :
    cnj a (algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r) =
      algebraMap E (Matrix (Fin n) (Fin n) (w.adicCompletion E)) r := by
  rw [cnj_apply, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, smul_mul_assoc, Matrix.mul_one,
    Units.inv_mul]

private def iotaAt (S : Setup A n p) (w : Plc E) (a : GL (Fin n) (w.adicCompletion E)) :
    S.G.C →ₐ[S.G.F] Matrix (Fin S.G.n) (Fin S.G.n) (w.adicCompletion E) :=
  { (cnj a).comp (RingHom.mapMatrix (algebraMap E (w.adicCompletion E))) with
    commutes' := fun r => (congrArg (cnj a) (alg_mat n w r)).trans (cnj_alg a r) }

private def kap0 (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E →+* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
  ((cnj (aw T w)).comp (RingHom.mapMatrix (rd T w hp))).comp (T.μ : _ →+* _)

private theorem rd_one (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (x : E) :
    rd T w hp ((1 : AfP p) ⊗ₜ x) = algebraMap E (w.adicCompletion E) x := by
  rw [← T.Φ_E x, rd_Φ]
  rfl

private theorem map_mu (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (y : Matrix (Fin n) (Fin n) E) :
    (T.μ ((1 : AfP p) ⊗ₜ[ℚ] y)).map (rd T w hp) = y.map (algebraMap E (w.adicCompletion E)) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, T.mu, rd_one, Matrix.map_apply]

private theorem map_Φ (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (M : Matrix (Fin n) (Fin n) (Af E)) :
    (M.map T.Φ).map (rd T w hp) = M.map (pLoc E w) := by
  apply Matrix.ext
  intro i k
  rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, rd_Φ]

private theorem at_eq (T : Tr S) (w : Plc E) (hp : (p : 𝓞 E) ∉ w.asIdeal) (g : GUf E n) :
    cnj (aw T w) ((T.μ (S.mx (T.j g))).map (rd T w hp)) = (comp w g).val := by
  have h2 : aw T w * comp w g * (aw T w)⁻¹ = GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have h1 : (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val = (T.a * mat g * T.a⁻¹).val.map (pLoc E w) := rfl
  rw [T.j_mx g, map_Φ, ← h1, ← h2, cnj_apply]
  simp [Matrix.mul_assoc]

end UpperTheory.Gal.Spc

open UpperTheory.Gal.Spc in
theorem UpperTheory.Gal.Spc.plTr :
    UpperTheory.Gal.Spc.PlTr := by
  intro E _ _ _ A n p _ S T w hp
  refine ⟨⟨kap0 T w hp, iotaAt S w (aw T w), fun y => ?_⟩, fun g => at_eq T w hp g⟩
  exact congrArg (cnj (aw T w)) (map_mu T w hp y)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FacCont
section
set_option autoImplicit false

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef
open GlobalTheory.CuspRep (pLoc)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw mat)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo.Pl
open scoped TensorProduct Classical Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Spc

private theorem small_of_nhds {E : Type} [Field E] [NumberField E] (w : Plc E) {U : Set (w.adicCompletion E)}
    (hU : U ∈ 𝓝 (0 : w.adicCompletion E)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : w.adicCompletion E, Valued.v x ≤ Valued.v (M : w.adicCompletion E) → x ∈ U := by
  obtain ⟨γ, -, hγ⟩ := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_iff.1 hU
  have hball := (Valued.hasBasis_nhds_zero (w.adicCompletion E) _).mem_of_mem (i := γ) trivial
  have hN0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hlt : Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) < 1 := by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w _).2 hm
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E)) =
        w.valuation E (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have h3 : algebraMap E (w.adicCompletion E) (((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) : E) =
        ((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) := by simp
    rw [h3] at h2
    rw [h2]
    exact h1
  obtain ⟨m, hm⟩ := ((Valued.tendsto_zero_pow_of_v_lt_one hlt).eventually hball).exists
  refine ⟨Ideal.absNorm w.asIdeal ^ m, Nat.pos_of_ne_zero (pow_ne_zero _ hN0), fun x hx => hγ ?_⟩
  have hx' : Valued.v x ≤ Valued.v (((Ideal.absNorm w.asIdeal : ℕ) : w.adicCompletion E) ^ m) := by
    simpa using hx
  exact lt_of_le_of_lt ((Valuation.restrict_le_iff _).2 hx') hm

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.facCont :
    UpperTheory.Gal.Spc.FacCont := by
  intro E _ _ _ A n p _ S F w L hL
  have hI := pKNIff (pLatCoord pRepLaws)
  have key : ∀ M : ℕ, 0 < M → ∀ k ∈ S.L.KN M, Cong1 M w.1 (F.a w.1 * L.pr k * (F.a w.1)⁻¹) := by
    intro M hM k hk
    obtain ⟨g, rfl⟩ := F.surj k
    have h1 : S.L.CongOne M (F.tr.j g) := by rw [← F.j_tr]; exact hk.1
    have h2 := ((hI E A n p S F.tr g).2 M hM).1 h1 w.1 w.2.2
    have h3 : UpperTheory.Gal.CertificateRingHomMap.comp w.1 g = GeneralLinearGroup.map (pLoc E w.1) (mat g) := rfl
    rw [hL.1 g, F.a_tr, h3]
    simpa [map_mul, map_inv] using h2
  have hopen : ∀ M : ℕ, 0 < M → (S.L.KN M : Set S.G.GAf) ∈ 𝓝 (1 : S.G.GAf) := by
    intro M hM
    obtain ⟨K, hK⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p S.D S.G S.L M hM
    have ho : IsOpen (S.L.KN M : Set S.G.GAf) := hK ▸ K.K.isOpen
    exact ho.mem_nhds (one_mem _)

  have hent : ∀ i j, Filter.Tendsto (fun k => ((F.a w.1 * L.pr k * (F.a w.1)⁻¹).val - 1) i j) (𝓝 (1 : S.G.GAf)) (𝓝 0) := by
    intro i j U hU
    obtain ⟨M, hM, hsm⟩ := small_of_nhds w.1 hU
    exact Filter.mem_map.2 (Filter.mem_of_superset (hopen M hM) fun k hk => hsm _ (key M hM k hk i j))
  have hmat : Filter.Tendsto (fun k => (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val) (𝓝 (1 : S.G.GAf))
      (𝓝 (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E))) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have := (hent i j).add_const ((1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j)
    simpa [Matrix.sub_apply] using this
  have hval : ContinuousAt (fun k => (L.pr k).val) (1 : S.G.GAf) := by
    have h := ((tendsto_const_nhds (x := ((F.a w.1)⁻¹).val)).mul hmat).mul (tendsto_const_nhds (x := (F.a w.1).val))
    have h1 : ((F.a w.1)⁻¹).val * 1 * (F.a w.1).val = (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) := by
      rw [mul_one]; exact (F.a w.1).inv_mul
    rw [h1] at h
    have h2 : ∀ k, ((F.a w.1)⁻¹).val * (F.a w.1 * L.pr k * (F.a w.1)⁻¹).val * (F.a w.1).val = (L.pr k).val := by
      intro k
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    simp only [h2] at h
    simpa [ContinuousAt] using h
  have hinv : ContinuousAt (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) (1 : S.G.GAf) := by
    have h : ContinuousAt (fun k : S.G.GAf => k⁻¹) 1 := continuous_inv.continuousAt
    have h' : ContinuousAt (fun k => (L.pr k).val) ((1 : S.G.GAf)⁻¹) := by simpa using hval
    have h2 : (fun k => (((L.pr k)⁻¹ : GL (Fin n) (w.1.adicCompletion E))).val) =
        (fun k => (L.pr k).val) ∘ (fun k : S.G.GAf => k⁻¹) := by
      funext k
      simp only [Function.comp, map_inv]
    rw [h2]
    exact ContinuousAt.comp h' h
  refine continuous_of_continuousAt_one L.pr ?_
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  exact hval.prodMk (MulOpposite.continuous_op.continuousAt.comp hinv)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.FacEx
section
open NumberField IsDedekindDomain

theorem UpperTheory.Gal.Spc.facEx :
    UpperTheory.Gal.Spc.FacEx := by
  intro E _ _ _ A n p _ S F w
  refine ⟨F.tr.at UpperTheory.Gal.W2.Seed.pLocComm w.1 w.2.1 w.2.2, fun g => ?_, fun y => ?_⟩
  · have h := (F.tr.j_eq (F.tr.sec (F.j g)) g).1 (by rw [F.j_tr]; exact F.tr.j_sec _) w.1 w.2.2
    exact h
  · rw [F.j_tr]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SepConj
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep
open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.Spc

section LinAlg

variable {K : Type*} [Field K] {m : ℕ}

private theorem sep_of_mul_closed [IsAlgClosed K] {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  classical
  have hdet : M.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    by_cases hm : m = 0
    · subst hm
      simp [Matrix.det_isEmpty] at h0
    · exact pow_ne_zero _ ha this.symm
  have hroot : ∀ x ∈ M.charpoly.roots, x ≠ 0 ∧ a / x ∈ N.charpoly.roots := by
    intro x hx
    have hx0 : M.charpoly.eval x = 0 := (Polynomial.mem_roots'.1 hx).2
    rw [Matrix.eval_charpoly] at hx0
    have hne : x ≠ 0 := by
      rintro rfl
      apply hdet
      simpa [Matrix.det_neg] using hx0
    refine ⟨hne, Polynomial.mem_roots'.2 ⟨(Matrix.charpoly_monic N).ne_zero, ?_⟩⟩
    show N.charpoly.eval (a / x) = 0
    rw [Matrix.eval_charpoly]
    have e : Matrix.scalar (Fin m) (a / x) - N = (-x⁻¹) • (N * (Matrix.scalar (Fin m) x - M)) := by
      rw [Matrix.mul_sub, h, Matrix.scalar_apply, Matrix.scalar_apply]
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply] <;> field_simp <;> ring
    rw [e, Matrix.det_smul, Matrix.det_mul, hx0, mul_zero, mul_zero]
  have hnd : M.charpoly.roots.Nodup := Polynomial.nodup_roots hM
  have hcM : M.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits M.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcN : N.charpoly.roots.card = m := by
    have := Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits N.charpoly)
    rw [this, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hinj : Set.InjOn (fun x : K => a / x) (M.charpoly.roots.toFinset : Set K) := by
    intro x hx y hy hxy
    have hx0 := (hroot x (by simpa using hx)).1
    have hy0 := (hroot y (by simpa using hy)).1
    have hxy' : a * x⁻¹ = a * y⁻¹ := by simpa only [div_eq_mul_inv] using hxy
    exact inv_injective (mul_left_cancel₀ ha hxy')
  have hsub : M.charpoly.roots.toFinset.image (fun x : K => a / x) ⊆ N.charpoly.roots.toFinset := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Multiset.mem_toFinset.2 (hroot x (Multiset.mem_toFinset.1 hx)).2
  have hle : m ≤ N.charpoly.roots.toFinset.card := by
    have h1 := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj, Multiset.toFinset_card_of_nodup hnd, hcM] at h1
  have hndN : N.charpoly.roots.Nodup := by
    rw [← Multiset.dedup_card_eq_card_iff_nodup]
    refine le_antisymm (Multiset.card_le_card (Multiset.dedup_le _)) ?_
    rw [hcN]
    exact hle
  exact (Polynomial.nodup_roots_iff_of_splits (Matrix.charpoly_monic N).ne_zero (IsAlgClosed.splits _)).1 hndN

private theorem sep_of_mul {M N : Matrix (Fin m) (Fin m) K} {a : K} (ha : a ≠ 0)
    (h : N * M = a • (1 : Matrix (Fin m) (Fin m) K)) (hM : M.charpoly.Separable) : N.charpoly.Separable := by
  have h' : N.map (algebraMap K (AlgebraicClosure K)) * M.map (algebraMap K (AlgebraicClosure K)) =
      algebraMap K (AlgebraicClosure K) a • (1 : Matrix (Fin m) (Fin m) (AlgebraicClosure K)) := by
    rw [← Matrix.map_mul, h]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h2 := sep_of_mul_closed (K := AlgebraicClosure K) (a := algebraMap K (AlgebraicClosure K) a)
    (by simpa using ha) h' (by rw [Matrix.charpoly_map]; exact hM.map)
  rw [Matrix.charpoly_map] at h2
  exact (Polynomial.separable_map _).1 h2

end LinAlg

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.sepConj :
    UpperTheory.Gal.Spc.SepConj := by
  intro E _ _ _ n g w hw
  have h0 : (g.1.1.val.map (conjFin (conjE E)))ᵀ * g.1.1.val =
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ) • (1 : Matrix (Fin n) (Fin n) _) := g.2
  have h1 := congrArg (RingHom.mapMatrix (pLoc E w)) h0
  rw [map_mul] at h1
  have ha : pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) ≠ 0 :=
    ((g.1.2.isUnit.map (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E)).map (pLoc E w)).ne_zero
  have h2 : (((UpperTheory.Gal.CertificateRingHomMap.comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (conjE E) w))ᵀ) * (UpperTheory.Gal.CertificateRingHomMap.comp w g).val =
      pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (g.1.2 : UpperTheory.Gal.CertificateRingHomMap.AfQ)) • (1 : Matrix (Fin n) (Fin n) _) := by
    refine Eq.trans ?_ (h1.trans ?_)
    · congr 1
    · ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have h3 := UpperTheory.Gal.Spc.sep_of_mul ha h2 hw
  rw [Matrix.charpoly_transpose, Matrix.charpoly_map] at h3
  exact (Polynomial.separable_map _).1 h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SplitC
section
set_option autoImplicit false

namespace UpperTheory.Gal.Spc

open UpperTheory.Gal.W2.Seed GlobalTheory.LKTrip GlobalTheory.UPel.HT

private def splitEquiv {X M : Type} [Group X] [Group M] (L : Loc X M) : X ≃* M × L.pr.ker where
  toFun g := (L.pr g, ⟨(L.loc (L.pr g))⁻¹ * g, by simp [MonoidHom.mem_ker, L.pr_loc]⟩)
  invFun x := L.loc x.1 * (x.2 : X)
  left_inv g := by simp
  right_inv x := by
    obtain ⟨m, h, hh⟩ := x
    have hh' : L.pr h = 1 := hh
    ext <;> simp [L.pr_loc, hh']
  map_mul' g h := by
    have hc : L.pr ((L.loc (L.pr g))⁻¹ * g) = 1 := by simp [L.pr_loc]
    have key := L.comm (L.pr h)⁻¹ _ hc
    rw [map_inv] at key
    refine Prod.ext (map_mul _ _ _) (Subtype.ext ?_)
    show (L.loc (L.pr (g * h)))⁻¹ * (g * h) = (L.loc (L.pr g))⁻¹ * g * ((L.loc (L.pr h))⁻¹ * h)
    rw [← mul_assoc ((L.loc (L.pr g))⁻¹ * g), ← key]
    simp [mul_assoc]

private theorem t2Space_hTGroup_gAf {p : ℕ} [Fact p.Prime] (G : HTGroup p) : T2Space G.GAf := by
  haveI := GlobalTheory.GfTop.t2Space_afP p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_locallyCompactSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_totallyDisconnectedSpace p
  haveI := GlobalTheory.GfTop.finiteAdeleRingAway_secondCountableTopology p
  exact (GlobalTheory.GfTop.upts_props G.star (AfP p)).2.1

theorem splitC : SplitC := by
  intro p _ G Lv k _ _ _ _ P L hcont hat Kw hKo hKc hF
  haveI := t2Space_hTGroup_gAf G
  have hker : IsClosed (L.pr.ker : Set G.GAf) := isClosed_singleton.preimage hcont
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨splitEquiv L, fun g => (hat g).symm, Kw, (Lv.K : Subgroup G.GAf).subgroupOf L.pr.ker,
      hKo, hKc, ?_, ?_, ?_⟩, fun g h => rfl⟩
  · exact Lv.K.isOpen.preimage continuous_subtype_val
  · exact hker.isClosedEmbedding_subtypeVal.isCompact_preimage Lv.compact
  · ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨hF.2 g hg, ?_⟩
      show (L.loc (L.pr g))⁻¹ * g ∈ (Lv.K : Subgroup G.GAf)
      exact mul_mem (inv_mem (hF.1 _ (hF.2 g hg))) hg
    · rintro ⟨hm, hh⟩
      exact ⟨L.loc x.1 * (x.2 : G.GAf), mul_mem (hF.1 _ hm) hh,
        (splitEquiv L).apply_symm_apply x⟩

end UpperTheory.Gal.Spc
end


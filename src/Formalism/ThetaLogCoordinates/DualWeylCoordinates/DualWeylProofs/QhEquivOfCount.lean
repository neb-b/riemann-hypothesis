module

public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhDetZpowMem

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      exact (not_le.mpr hc) (hm.2.trans (hmu hmt))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
  · intro h
    have hsub : Finset.Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ m, h.trans (hmu hm)⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega

lemma qh_le_last [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  rw [Fin.le_iff_val_le_val]
  show a.val ≤ n - 1
  have := a.isLt
  omega

lemma qh_count [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) :
    ((TCols mu).filter (fun c => t.val < colH mu c)).card = (mu t - mu (lastIdx n)).toNat := by
  have h0 : mu t ≤ mu 0 := hmu (by first | exact Fin.zero_le _ | (rw [Fin.le_iff_val_le_val]; simp))
  have hset : (TCols mu).filter (fun c => t.val < colH mu c) =
      Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    simp only [Finset.mem_filter, qh_lt_colH_iff hmu, TCols, Finset.mem_Ioc]
    exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2.trans h0⟩, hh.2⟩⟩
  rw [hset, Int.card_Ioc]

lemma qh_weight_sum [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun _ : Fin n => mu (lastIdx n)) +
      ∑ c : ↥(TCols mu), (fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0) = mu := by
  funext a
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_coe_sort (TCols mu) (fun c => if a.val < colH mu c then (1 : ℤ) else 0),
    Finset.sum_boole, qh_count hmu a,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmu (qh_le_last a)))]
  ring

lemma qh_mapCoord_alg (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ _ P) = algebraMap _ _ (MvPolynomial.map (Int.castRingHom R) P) := by
  first
    | (rw [mapCoord, IsLocalization.Away.AwayMap.lift_eq]; try rfl; done)
    | (rw [mapCoord, IsLocalization.Away.lift_eq]; try rfl; done)
    | (simp [mapCoord]; done)
    | (unfold mapCoord; exact IsLocalization.lift_eq _ _)

lemma qh_mapCoord_detU (z : ℤ) :
    mapCoord R ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qhDet R n ^ z : (GLCoord R n)ˣ) : GLCoord R n) := by
  have h1 : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    apply Units.ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R)) (genMat ℤ n),
      genMat_map_coord]
  rw [← h1, ← map_zpow (Units.map (mapCoord (n := n) R).toMonoidHom) (detU n) z, Units.coe_map]
  try rfl

lemma qh_can_emb [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have hmem : ∀ x : Fin (colH mu c), Fin.castLE (colH_le mu c) x ∈ (canT mu c).1 := by
    intro x
    first
      | (simp only [canT, Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨x, rfl⟩)
      | simp [canT]
  have hmono : StrictMono (Fin.castLE (colH_le mu c)) := by
    intro x y hxy
    rw [Fin.lt_iff_val_lt_val] at hxy ⊢
    exact hxy
  exact (congrFun (Finset.orderEmbOfFin_unique (canT mu c).2 hmem hmono) a).symm

lemma qh_mapCoord_minor [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (S : Finset (Fin n))
    (hS : S.card = colH mu c) :
    mapCoord R (minorC (canT mu c).1 S (canT mu c).2 hS) =
      qhN R (colH mu c) (colH_le mu c) (fun q => S.orderEmbOfFin hS q) := by
  unfold minorC qhN
  rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R))]
  congr 2
  ext p q
  first
    | (simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, genMat, MvPolynomial.map_X,
        qh_can_emb]; done)
    | simp [genMat, qh_can_emb]

lemma qh_mapCoord_brk [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord R (brk mu I) = ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
      ∏ c : ↥(TCols mu), qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q) := by
  first
    | (simp only [brk, TMat]
       rw [map_mul, map_prod, qh_mapCoord_detU]
       congr 1
       refine Finset.prod_congr rfl (fun c _ => ?_)
       exact qh_mapCoord_minor mu c _ _)
    | (simp only [brk, TMat, map_mul, map_prod, qh_mapCoord_detU,
        qh_mapCoord_minor])

lemma qh_brk_mem [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    mapCoord R (brk mu I) ∈ inducedSections R mu := by
  rw [qh_mapCoord_brk]
  have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) (mu (lastIdx n)))
    (qh_prod_mem (R := R) (Finset.univ : Finset ↥(TCols mu))
      (fun c => qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q))
      (fun c => fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0)
      (fun c _ => qh_N_mem (R := R) (colH mu c) (colH_le mu c) _))
  first
    | (rw [qh_weight_sum hmu] at h; exact h)
    | (convert h using 2; exact (qh_weight_sum hmu).symm)

end Formalism.InvariantFactorPaths.ColumnFamilies

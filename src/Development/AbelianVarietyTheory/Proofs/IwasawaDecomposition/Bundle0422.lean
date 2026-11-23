module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdBideterminantsEqColumnChoiceMinorProduct
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

noncomputable section

namespace GlobalTheory.Mem.CanonicalSurjection

theorem exists_equiv_of_counts {A B : Type} [Fintype A] [Fintype B] (a : A → ℕ) (b : B → ℕ)
    (hb : ∀ x, 0 < b x)
    (h : ∀ t : ℕ, (Finset.univ.filter fun x => t < a x).card = (Finset.univ.filter fun x => t < b x).card) :
    ∃ e : {x // 0 < a x} ≃ B, ∀ x, b (e x) = a x.1 := by
  classical
  have key : ∀ {C : Type} [Fintype C] (f : C → ℕ) (c : ℕ), 0 < c →
      (Finset.univ.filter fun x => f x = c).card + (Finset.univ.filter fun x => c < f x).card =
        (Finset.univ.filter fun x => c - 1 < f x).card := by
    intro C _ f c hc
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      omega
  have fib : ∀ c, Fintype.card {x : {x // 0 < a x} // a x.1 = c} = Fintype.card {y // b y = c} := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · have h1 : IsEmpty {x : {x // 0 < a x} // a x.1 = 0} := ⟨fun x => by have := x.1.2; have := x.2; omega⟩
      have h2 : IsEmpty {y // b y = 0} := ⟨fun y => by have := hb y.1; have := y.2; omega⟩
      simp
    · have e1 : Fintype.card {x : {x // 0 < a x} // a x.1 = c} = (Finset.univ.filter fun x => a x = c).card := by
        rw [← Fintype.card_subtype]
        refine Fintype.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, by have := x.2; omega⟩, x.2⟩, ?_, ?_⟩
        · intro x; rfl
        · intro x; rfl
      have e2 : Fintype.card {y // b y = c} = (Finset.univ.filter fun x => b x = c).card := by
        rw [Fintype.card_subtype]
      rw [e1, e2]
      have k1 := key a c hc
      have k2 := key b c hc
      have h1 := h c
      have h2 := h (c - 1)
      omega
  refine ⟨Equiv.ofFiberEquiv (f := fun x : {x // 0 < a x} => a x.1) (g := b)
    (fun c => Fintype.equivOfCardEq (fib c)), fun x => ?_⟩
  exact Equiv.ofFiberEquiv_map _ x

theorem card_colLen_gt (μ : YoungDiagram) (t : ℕ) :
    (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card = μ.rowLen t := by
  classical
  have hle : μ.rowLen t ≤ μ.rowLen 0 := μ.rowLen_anti 0 t (Nat.zero_le _)
  have : (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c) =
      Finset.univ.filter fun c : Fin (μ.rowLen 0) => c.val < μ.rowLen t := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  rw [this, ← Fintype.card_subtype]
  rw [Fintype.card_congr (β := Fin (μ.rowLen t))
    ⟨fun c => ⟨c.1.1, c.2⟩, fun c => ⟨⟨c.1, by have := c.2; omega⟩, c.2⟩, fun _ => rfl, fun _ => rfl⟩]
  simp

theorem minor_cast {K : Type} [CommRing K] {N h h' : ℕ} (Y : Matrix (Fin N) (Fin N) K) (e : h = h') (hN : h ≤ N)
    (I : Fin h → Fin N) :
    Matrix.det (Matrix.of fun p q : Fin h => Y (I p) (Fin.castLE hN q)) =
      Matrix.det (Matrix.of fun i j : Fin h' => GL3Columns.colsOf Y (I (Fin.cast e.symm i)) (j : ℕ)) := by
  subst e
  congr 1
  ext p q
  have hq : (q : ℕ) < N := lt_of_lt_of_le q.2 hN
  simp [GL3Columns.colsOf, hq, Fin.castLE]

theorem bidFns_eq_minors {K : Type} [CommRing K] {N : ℕ} (μ : YoungDiagram) (ν : Fin N → ℕ)
    (h1 : ∀ r : Fin N, μ.rowLen r = ν r) (h2 : ∀ r, N ≤ r → μ.rowLen r = 0)
    (g : Matrix (Fin N) (Fin N) K → K) (hg : g ∈ bideterminantFunctionsOfShape K N ν) :
    ∃ J : ∀ c : Fin (μ.rowLen 0), Fin (μ.colLen c) ↪o Fin N, ∀ Y : Matrix (Fin N) (Fin N) K,
      g Y = ∏ c : Fin (μ.rowLen 0), Matrix.det (Matrix.of fun i j : Fin (μ.colLen c) =>
        GL3Columns.colsOf Y (J c i) (j : ℕ)) := by
  classical
  obtain ⟨Kc, sz, hsz, I, hshape, hI, rfl⟩ := hg
  have count : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun c : Fin (μ.rowLen 0) => t < μ.colLen c).card := by
    intro t
    rw [card_colLen_gt]
    by_cases ht : t < N
    · have := congrFun hshape ⟨t, ht⟩
      rw [h1 ⟨t, ht⟩, ← this]
      simp only [Formalism.GradedWeylDivisibility.shapeDeg]
    · rw [h2 t (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      have := hsz k
      omega
  have hpos : ∀ c : Fin (μ.rowLen 0), 0 < μ.colLen c := by
    intro c
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
    exact c.2
  obtain ⟨e, he⟩ := exists_equiv_of_counts sz (fun c : Fin (μ.rowLen 0) => μ.colLen c) hpos count
  have hk : ∀ c, sz (e.symm c).1 = μ.colLen c := by
    intro c
    have := he (e.symm c)
    simpa using this.symm
  refine ⟨fun c => OrderEmbedding.ofStrictMono (fun i => I (e.symm c).1 (Fin.cast (hk c).symm i))
    (fun i j hij => hI _ (by simpa using hij)), fun Y => ?_⟩
  have hone : ∀ k, ¬ 0 < sz k → Matrix.det (Matrix.of fun p q : Fin (sz k) =>
      Y (I k p) (Fin.castLE (hsz k) q)) = 1 := by
    intro k hk0
    have h0 : sz k = 0 := by omega
    haveI : IsEmpty (Fin (sz k)) := by rw [h0]; infer_instance
    exact Matrix.det_isEmpty
  have hev : MvPolynomial.eval (fun v : Fin N × Fin N => Y v.1 v.2) (Formalism.GradedWeylDivisibility.bideterminant K sz hsz I) =
      ∏ k, Matrix.det (Matrix.of fun p q : Fin (sz k) => Y (I k p) (Fin.castLE (hsz k) q)) := by
    simp only [Formalism.GradedWeylDivisibility.bideterminant, Formalism.GradedWeylDivisibility.initMinor, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp
  show MvPolynomial.eval _ _ = _
  rw [hev, ← Finset.prod_filter_of_ne (p := fun k => 0 < sz k)
    (fun k _ hne => by by_contra hc; exact hne (hone k hc)), Finset.prod_subtype _ (p := fun k => 0 < sz k) (by simp)]
  refine (Fintype.prod_equiv e.symm _ _ fun c => ?_).symm
  exact (minor_cast Y (hk c) (hsz _) (I (e.symm c).1)).symm

theorem prod_bidFns_eq_minY : ∀ (D : D7) (K : Type) [CommRing K] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (ν : D.what₂.Tau → Fin N → ℕ), NuFits D nu ν → ∀ g : D.what₂.Tau → Matrix (Fin N) (Fin N) K → K,
    (∀ τ, g τ ∈ bideterminantFunctionsOfShape K N (ν τ)) → ∃ J : KM.ColChoice N nu, ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) K,
      ∏ τ, g τ (y τ) = GL3Columns.minY N nu J (fun s => GL3Columns.colsOf (y (tauPl D s))) := by
  classical
  intro D K _ N nu ν hfit g hg
  have hJ := fun z => bidFns_eq_minors (nu z) (ν (tauPl D z)) (hfit.1 z) (hfit.2 z) (g (tauPl D z)) (hg _)
  choose J hJ using hJ
  refine ⟨J, fun y => ?_⟩
  refine ((tauPl_bij D).prod_comp (fun τ => g τ (y τ))).symm.trans ?_
  exact Finset.prod_congr rfl fun z _ => hJ z (y (tauPl D z))

end GlobalTheory.Mem.CanonicalSurjection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMUMatMove
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjMove

section Ring

variable {A R k : Type} [CommRing A] [CommRing R] [CommRing k] {m n : ℕ}

def adj (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) :
    Matrix (Fin m) (Fin n) R := C * (Matrix.of Z).map φ * B

theorem adj_move (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B Y : Matrix (Fin n) (Fin n) R)
    (u : Matrix (Fin n) (Fin n) A) (h : (u.map φ)ᵀ * B * Y = B) (M : ℕ) (Z Z' w : Fin m → Fin n → A)
    (hZ : ∀ b, u *ᵥ Z' b = Z b + M • w b) : adj φ C B Z' = (adj φ C B Z + M • adj φ C B w) * Y := by
  have e : (Matrix.of Z).map φ + M • (Matrix.of w).map φ = (Matrix.of Z').map φ * (u.map φ)ᵀ := by
    ext b a
    have := congrArg φ (congrFun (hZ b) a)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_nsmul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, ← this, mul_comm]
  unfold adj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add, e]
  conv_lhs => rw [← h]
  simp only [Matrix.mul_assoc]

theorem adj_apply (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A)
    (b' : Fin m) (a : Fin n) : adj φ C B Z b' a = ∑ b, C b' b * ∑ j, φ (Z b j) * B j a := by
  unfold adj
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]

theorem red_eq (S : Subring R) (ρ : S →+* k) (M : ℕ) (hM : (M : k) = 0) (X X' W : Matrix (Fin m) (Fin n) R)
    (y : Matrix (Fin n) (Fin n) S) (hX : ∀ i j, X i j ∈ S) (hX' : ∀ i j, X' i j ∈ S) (hW : ∀ i j, W i j ∈ S)
    (h : X' = (X + M • W) * y.map S.subtype) (i : Fin m) (j : Fin n) :
    ρ ⟨X' i j, hX' i j⟩ = ∑ a, ρ ⟨X i a, hX i a⟩ * ρ (y a j) := by
  have e : (⟨X' i j, hX' i j⟩ : S) = ∑ a, (⟨X i a, hX i a⟩ + M • ⟨W i a, hW i a⟩) * y a j := by
    apply Subtype.ext
    simp [h, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_add (f := _), map_nsmul, nsmul_eq_mul, hM, zero_mul, add_zero]

def lft (c : R) (P Q : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R := c • (P * Q)

theorem entry_eq {E : Type} [CommRing E] (f : E →+* R) (φ : A →+* R) (c : R) (P : Matrix (Fin m) (Fin m) R)
    (Q : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin n) E) (G : Matrix (Fin n) (Fin n) E)
    (β : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) (h : ∀ b a, f (X b a) = φ (Z b a)) :
    (fun b a => c * (P * (Q * X * G).map f * β) b a) = adj φ (lft c P (Q.map f)) (G.map f * β) Z := by
  have e1 : X.map f = (Matrix.of Z).map φ := Matrix.ext h
  unfold adj lft
  rw [Matrix.smul_mul, Matrix.smul_mul, ← e1, Matrix.map_mul, Matrix.map_mul]
  ext b a
  simp only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul]

theorem unit_rel_ring (S : Subring R) (σ : A →+* A) (s : A →+* R) (J : Matrix (Fin n) (Fin n) A) (u : GL (Fin n) A)
    (β : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ∈ Formalism.UG.UJ σ J)
    (hy : β * Formalism.UG.bc S.subtype y * β⁻¹ = Formalism.UG.bc s u) :
    (u.1.map (s.comp σ))ᵀ * (J.map s * β.1) * y.1.map S.subtype = J.map s * β.1 := by
  have h1 : β * Formalism.UG.bc S.subtype y = Formalism.UG.bc s u * β := by rw [← hy, inv_mul_cancel_right]
  have h2 : β.1 * y.1.map S.subtype = u.1.map s * β.1 := congrArg Units.val h1
  have h4 : (u.1.map σ)ᵀ * J * u.1 = J := hu
  have h5 := congrArg (fun N => Matrix.map N s) h4
  simp only [Matrix.map_mul] at h5
  have h6 : (u.1.map (s.comp σ))ᵀ * J.map s * u.1.map s = J.map s := h5
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h6]

theorem adj_int_ring (S : Subring R) (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (s : Set (Fin n → A)) (La : Type) [Zero La] (v : La → Fin n → A) (v0 : ∀ j, v 0 j = 0)
    (h : ∀ x : Fin m → La, ∀ i j, adj φ C B (fun b => v (x b)) i j ∈ S)
    (hs : ∀ z ∈ s, ∃ t ∈ S, ∃ l, ∀ j, φ (z j) = t * φ (v l j))
    (w : Fin m → Fin n → A) (hw : ∀ b, w b ∈ AddSubgroup.closure s) (b' : Fin m) (a : Fin n) : adj φ C B w b' a ∈ S := by
  rw [adj_apply]
  refine sum_mem fun b _ => ?_
  have key : ∀ z ∈ AddSubgroup.closure s, C b' b * ∑ j, φ (z j) * B j a ∈ S := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, l, hl⟩ := hs z hz
      have h1 := h (Pi.single b l) b' a
      rw [adj_apply, Finset.sum_eq_single b] at h1
      · have h2 := mul_mem ht h1
        rw [Pi.single_eq_same, mul_left_comm, Finset.mul_sum] at h2
        simpa only [hl, mul_assoc] using h2
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc]
        simp [v0]
      · simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]
      exact add_mem hx hy
    | neg x _ hx =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
      exact neg_mem hx
  exact key _ (hw b)

end Ring

variable {D : D7}

noncomputable def barSwap (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Lev.swapAE D).comp (sigR (Af D.host.F) D.sp.cm.sig)

theorem barSwap_tmul (a : Af D.host.F) (x : D.host.E) :
    barSwap D (a ⊗ₜ[D.host.F] x) = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * barSwap D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) := by
  change D.sp.cm.sig x ⊗ₜ[D.host.F] a = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * (D.sp.cm.sig x ⊗ₜ[D.host.F] 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem uMat_eq (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) :
    uMat S T βS βT e X = adj (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D)))
      (T.gram.map (eToEAf D) * βT.1) fun b => finVec T (X b) :=
  entry_eq (eToEAf D) (barSwap D) _ _ _ _ _ _ _ fun _ _ => rfl

theorem unit_rel (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (u : GA D T)
    (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (hy : frGL βT y = Lev.finE T u) :
    ((finHom T u).1.map (barSwap D))ᵀ * (T.gram.map (eToEAf D) * βT.1) * y.1.map (Subring.subtype _) =
      T.gram.map (eToEAf D) * βT.1 :=
  unit_rel_ring _ (sigR (Af D.host.F) D.sp.cm.sig) (Lev.swapAE D) (JR (Af D.host.F) T.gram) (finHom T u) βT y
    (GlobalTheory.UnitarySplit.finHom_mem T u) hy

theorem adj_int {m : ℕ} (T : HSp D) (C : Matrix (Fin m) (Fin m) (EAf D)) (B : Matrix (Fin T.rank) (Fin T.rank) (EAf D))
    (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E))
    (h : ∀ x : Fin m → La, IsIntM (adj (barSwap D) C B fun b => finVec T (ι (x b))))
    (w : Fin m → Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : ∀ b, w b ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι)) : IsIntM (adj (barSwap D) C B w) := by
  refine adj_int_ring _ (barSwap D) C B _ La (fun l => finVec T (ι l)) (fun j => ?_) h ?_ w hw
  · show (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι 0 j) = 0
    rw [LinearMap.map_zero]
    exact TensorProduct.tmul_zero _ _
  · rintro z ⟨α, hα, _, ⟨l, rfl⟩, rfl⟩
    exact ⟨(1 : D.host.E) ⊗ₜ[D.host.F] α, Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩), l,
      fun j => barSwap_tmul α (ι l j)⟩


set_option maxHeartbeats 800000 in
theorem redM_uMat_move : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (u : GA D T) (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), frGL βT y = Lev.finE T u → ∀ (M : ℕ) (PP : Pl D.host.E), (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x x' : Fin S.rank → La, (∀ b, ∃ w ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι), (finHom T u).1.mulVec (finVec T (ι (x' b))) = finVec T (ι (x b)) + M • w) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) * y.1.map (resS D.host.F PP) := by
  intro D S T βS βT e La _ _ ι hint u y hy M PP hM x x' hx
  choose w hw hx using hx
  have hW := adj_int T _ _ La ι (fun x => by rw [← uMat_eq S T βS βT e]; exact hint x) w hw
  have hmv := adj_move (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D))) _ _ _ (unit_rel T βT u y hy) M
    (fun b => finVec T (ι (x b))) (fun b => finVec T (ι (x' b))) w hx
  rw [← uMat_eq S T βS βT e, ← uMat_eq S T βS βT e] at hmv
  have hM' : (M : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hM
  ext i j
  have := red_eq _ (resS D.host.F PP) M hM' _ _ _ y.1 (hint x) (hint x') hW hmv i j
  rw [Matrix.mul_apply]
  unfold redM
  rw [dite_eq_left (hint x' i j), this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (hint x i a)]
  rfl

end GlobalTheory.AdjMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem tup_sgHC_eq {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    Formalism.L2.Forms.sgHC R P i = (RowPar.of P).sgHC i := by
  have hi := i.2
  have hN : R.N R.m = (R.k + R.m) + R.m * R.t := N_eq_blocks R R.m
  unfold Formalism.L2.Forms.sgHC RowPar.sgHC
  congr 1
  by_cases h1 : (i : ℕ) < R.k - 1
  · rw [dite_eq_left h1, dite_eq_left h1]
    rfl
  · rw [dite_eq_right h1, dite_eq_right h1]
    have h2 : ((i : ℕ) - (R.k - 1)) / (R.t + 1) < R.m := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
      have := R.two_le_m
      have e : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
      have e' : R.m * R.t.succ = R.m * (R.t + 1) := rfl
      omega
    rw [dite_eq_left h2]
    split_ifs with h3
    · simp [RowPar.bAt, h2]
      rfl
    · simp [RowPar.eAt, h2]
      rfl

theorem tup_rowPar_eq (B : Base) (u : B.Word) (τ : Tau B.R) : RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ) := by
  unfold RowPar.of
  rw [B.hcW_v, B.hcW_b, B.hcW_e]

theorem fm_sg_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  intro B X I hI hP l Z u a τ i
  have h2 := (tup_sgHC_eq (B.hcW u τ) i).trans (congrArg (fun P => RowPar.sgHC P i) (tup_rowPar_eq B u τ))
  exact (RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ptC_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  intro B X I hI hP l Z u a Q K hQ hQ' hR z
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = (sgTG (D := I.rec7 l Z) (I.fm l u a) : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hc : ∀ c (s : (I.stX a).Stab c) (κ : K.lev.U), (K.y c).1 =
      bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 →
      ((K.lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
    intro c s κ e
    let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
    have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
    have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
    have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
        ((I.stX a).rep c).1.1 := by
      have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
        congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
      conv_rhs => rw [← e1]
      refine Eq.trans ?_ (smul_smul _ _ _).symm
      have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
          GLG (E := B.fields.E) (n := B.R.N B.R.m - 1) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
          FrmG.incl _ _ s.1 := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (inv_mul_cancel _).symm
        · exact (one_mul _).symm
        · exact (one_mul _).symm
      exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
    have hst := hR.stab c s
    let yc : GA B (B.R.N B.R.m - 1) := (K.y c).1
    let kk : GA B (B.R.N B.R.m - 1) := κ.1
    have e' : yc = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * yc * kk := by
      have h0 := e
      rw [show (K.stabI c s).1 = (I.stX a).gam c.1 s.1 from hst] at h0
      exact h0
    have hyk : yc * kk = ratAd B.host.F (s.1.1)⁻¹ * yc := by
      have e3 : ratAd B.host.F (s.1.1)⁻¹ =
          (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
        unfold ratAd
        rw [map_inv, map_inv]
        rfl
      rw [e3]
      conv_rhs => rw [e']
      group
    have hq : PtOf (yc * kk) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
      rw [hyk, hact]
      exact hp
    exact hR.chr c κ κ0 hgam hq
  letI : Algebra (I.rec7 l Z).host.F B.fields.E := (inferInstance : Algebra (I.rec7 l Z).host.F (I.rec7 l Z).host.E)
  exact mem_Fi_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT K.lev hemb hsg K.y K.y_bij K.stabI
    (fun c γ => K.stabI_range c γ) (fun c s => hR.stab c s) hc z

end GlobalTheory.Mem.Col2.TwP

end
end


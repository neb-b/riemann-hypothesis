module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0335
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliAuxiliaryStatement
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapRes

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b n : ℕ}

theorem map_emb₂ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : Fin a ⊕ Fin b ≃ Fin n)
    (g : GL (Fin a) R × GL (Fin b) R) :
    GeneralLinearGroup.map f (GlobalTheory.SmGL.emb₂ R e g) =
      GlobalTheory.SmGL.emb₂ S e (GeneralLinearGroup.map f g.1, GeneralLinearGroup.map f g.2) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  apply Units.ext
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  change f ((GlobalTheory.SmGL.emb₂ R e g : Matrix _ _ R) (e p) (e q)) = (GlobalTheory.SmGL.emb₂ S e _ : Matrix _ _ S) (e p) (e q)
  rw [val_emb₂, val_emb₂]
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb₂_swap {R : Type} [CommRing R] (e : Fin a ⊕ Fin b ≃ Fin n) (g₁ : GL (Fin a) R) (g₂ : GL (Fin b) R) :
    GlobalTheory.SmGL.emb₂ R ((Equiv.sumComm (Fin b) (Fin a)).trans e) (g₂, g₁) = GlobalTheory.SmGL.emb₂ R e (g₁, g₂) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  apply Units.ext
  rw [val_emb₂, val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb_infGL (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.SmGL.emb₂ (Ad E) e (infGL E a y, (1 : GL (Fin b) (Ad E))) =
      infGL E n (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)) := by
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_emb₂]; simp
  · rw [pFin_infGL, map_emb₂, pFin_infGL, map_one]
    exact map_one _

def blockL (e : Fin a ⊕ Fin b ≃ Fin n) : Lie E a →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (reindex e e (fromBlocks (Matrix.of x) 0 0 0))
      map_add' := fun x y => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp
      map_smul' := fun c x => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp }

theorem blockL_apply (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) (p q : Fin a ⊕ Fin b) :
    blockL e x (e p) (e q) = fromBlocks (Matrix.of x) 0 0 0 p q := by
  simp [blockL]

def shift (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) : Lie E n := (oneL E n - blockL e (oneL E a)) + blockL e x

theorem shift_one (e : Fin a ⊕ Fin b ≃ Fin n) : shift e (oneL E a) = oneL E n := by simp [shift]

theorem toL_emb (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    toL (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)).val = shift e (toL y.val) := by
  have val_emb₂ {c d : ℕ} (T : Type) [CommRing T] (ee : Fin c ⊕ Fin d ≃ Fin n)
      (g : GL (Fin c) T × GL (Fin d) T) :
      (GlobalTheory.SmGL.emb₂ T ee g).val =
        Matrix.reindex ee ee (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases ee.symm i with a | a <;> rcases ee.symm j with b | b <;> simp
  rw [val_emb₂]
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  simp only [shift, Pi.add_apply, Pi.sub_apply, blockL_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply]

theorem blockL_single (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    blockL e (toL (Matrix.single i j x)) = toL (Matrix.single (e (.inl i)) (e (.inl j)) x) := by
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rw [blockL_apply]
  change fromBlocks (Matrix.single i j x) 0 0 0 p q = Matrix.single (e (.inl i)) (e (.inl j)) x (e p) (e q)
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.single_apply]

def iota (e : Fin a ⊕ Fin b ≃ Fin n) : GA E a →* GA E n :=
  (GlobalTheory.SmGL.emb₂ (Ad E) e).comp (MonoidHom.inl _ _)

theorem iota_apply (e : Fin a ⊕ Fin b ≃ Fin n) (m : GA E a) : iota e m = GlobalTheory.SmGL.emb₂ (Ad E) e (m, 1) := rfl

theorem chart_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} {G : GA E a → ℂ} (h : ∀ m, G m = F (iota e m))
    (m : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) : chart G m x = chart F (iota e m) (shift e x) := by
  obtain ⟨u, hu⟩ := id hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, h, map_mul, ← toL_emb, chart_val, iota_apply e (infGL E a u), emb_infGL]

theorem lieD_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} (hF : F ∈ Sm E n) {G : GA E a → ℂ}
    (h : ∀ m, G m = F (iota e m)) (X : Lie E a) (m : GA E a) :
    lieD X G m = lieD (blockL e X) F (iota e m) := by
  have hd : HasFDerivAt (shift e) (blockL e : Lie E a →L[ℝ] Lie E n) (oneL E a) :=
    (blockL e).hasFDerivAt.const_add _
  have hc : HasFDerivAt (chart F (iota e m)) (fderiv ℝ (chart F (iota e m)) (oneL E n)) (shift e (oneL E a)) := by
    rw [shift_one]; exact (differentiableAt_chart hF _).hasFDerivAt
  have h2 := hc.comp (oneL E a) hd
  have h3 : chart G m =ᶠ[𝓝 (oneL E a)] chart F (iota e m) ∘ shift e := by
    filter_upwards [isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)] with x hx
    exact chart_eq e h m hx
  unfold lieD
  rw [h3.fderiv_eq, h2.fderiv]
  rfl

def relAlg (e : Fin a ⊕ Fin b ≃ Fin n) : Subalgebra ℂ (Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) where
  carrier := {p | ∀ (F : Sm E n) (G : Sm E a), (∀ m, G.1 m = F.1 (iota e m)) →
    ∀ m, (p.1 G).1 m = (p.2 F).1 (iota e m)}
  mul_mem' := fun hp hq F G h m => hp _ _ (hq F G h) m
  add_mem' := fun hp hq F G h m => congrArg₂ (· + ·) (hp F G h m) (hq F G h m)
  algebraMap_mem' := fun c F G h m => congrArg (c • ·) (h m)

theorem lie_mem (e : Fin a ⊕ Fin b ≃ Fin n) (X : Lie E a) :
    ((lie E a X, lie E n (blockL e X)) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  fun F _ h m => lieD_eq e F.2 h X m

theorem lieS_mem (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    ((lieS E a i j x, lieS E n (e (.inl i)) (e (.inl j)) x) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈
      relAlg e := by
  have := lie_mem e (toL (Matrix.single i j x))
  rwa [blockL_single] at this

theorem Eop_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (i j : Fin a) :
    ((Eop τ i j, Eop τ (e (.inl i)) (e (.inl j))) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  (relAlg e).smul_mem ((relAlg e).sub_mem (lieS_mem e i j _) ((relAlg e).smul_mem (lieS_mem e i j _) _)) _

theorem qdet_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (v : ℂ) :
    ((Formalism.REAL.qdet (Eop τ) v, Formalism.REAL.qdet (fun i j : Fin a => Eop τ (e (.inl i)) (e (.inl j))) v) :
      Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e := by
  let P := Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)
  let Z : Fin a → Fin a → P := fun i j => (Eop τ i j, Eop τ (e (.inl i)) (e (.inl j)))
  have h1 := map_qdet (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h2 := map_qdet (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h3 : Formalism.REAL.qdet Z v ∈ relAlg e := by
    refine (relAlg e).sum_mem fun σ _ => (relAlg e).mul_mem (intCast_mem (relAlg e) _)
      ((relAlg e).list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine (relAlg e).add_mem ?_ (Eop_mem e τ _ _)
    split_ifs
    · exact (relAlg e).algebraMap_mem _
    · exact (relAlg e).zero_mem
  convert h3 using 1
  exact Prod.ext h1.symm h2.symm

theorem aeval_mem (e : Fin a ⊕ Fin b ≃ Fin n) {z : Module.End ℂ (Sm E a)} {z' : Module.End ℂ (Sm E n)}
    (hz : (z, z') ∈ relAlg e) (q : Polynomial ℂ) :
    (Polynomial.aeval z q, Polynomial.aeval z' q) ∈ relAlg e := by
  have h1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h3 : Polynomial.aeval (z, z') q ∈ relAlg e := by
    rw [Polynomial.aeval_eq_sum_range]
    exact (relAlg e).sum_mem fun i _ => (relAlg e).smul_mem ((relAlg e).pow_mem hz i) _
  convert h3 using 1
  exact Prod.ext h1 h2

end GlobalTheory.CompanionTheory.CTFin.CapRes

namespace GlobalTheory.CompanionTheory.CTFin

open CapRes

theorem capelli_restrict : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  intro E _ _ _ r s τ u q F
  constructor
  · intro G h m
    exact aeval_mem (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (qdet_mem _ τ _) q F G h m
  · intro G h m
    have hι : ∀ m : GA E s, iota ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))) m =
        lev (Ad E) r s (1, m) := fun m => emb₂_swap _ _ _
    have := aeval_mem ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
      (qdet_mem _ τ (u + ((s : ℂ) - 1) / 2)) q F G (fun m => by rw [hι]; exact h m) m
    rw [hι] at this
    exact this

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapStable

theorem qdet_mem {a : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (h : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (h _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

def blockM {R : Type} [CommRing R] {r s : ℕ} (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    Matrix (Fin (r + s)) (Fin (r + s)) R :=
  Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (fromBlocks A 0 0 B)

theorem val_lev {R : Type} [CommRing R] {r s : ℕ} (g : GL (Fin r) R × GL (Fin s) R) :
    (lev R r s g).val = blockM g.1.val g.2.val :=
  GlobalTheory.SmGL.val_emb₂ R _ g

theorem blockM_map {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) (B : Matrix (Fin s) (Fin s) R) :
    (blockM A B).map p = blockM (A.map p) (B.map p) := by
  ext i j
  simp only [blockM, Matrix.map_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem map_lev {R S : Type} [CommRing R] [CommRing S] {r s : ℕ} (p : R →+* S)
    (g : GL (Fin r) R × GL (Fin s) R) :
    Matrix.GeneralLinearGroup.map p (lev R r s g) =
      lev S r s (Matrix.GeneralLinearGroup.map p g.1, Matrix.GeneralLinearGroup.map p g.2) := by
  apply Units.ext
  change (lev R r s g).val.map p = (lev S r s _).val
  rw [val_lev, val_lev, blockM_map]
  rfl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem infGL_lev (y : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
    infGL E (r + s) (lev (Cinf E) r s y) = lev (Ad E) r s (infGL E r y.1, infGL E s y.2) := by
  refine ga_ext ?_ ?_
  · rw [map_lev]; simp
  · rw [map_lev]; simp only [pFin_infGL, pFin_infGL]; exact (map_one _).symm

theorem blockM_add {R : Type} [CommRing R] {r s : ℕ} (A A' : Matrix (Fin r) (Fin r) R)
    (B B' : Matrix (Fin s) (Fin s) R) : blockM A B + blockM A' B' = blockM (A + A') (B + B') := by
  ext i j
  simp only [blockM, Matrix.add_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem blockM_smul {R : Type} [CommRing R] {r s : ℕ} (t : ℝ) [Module ℝ R] (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin s) (Fin s) R) : t • blockM A B = blockM (t • A) (t • B) := by
  ext i j
  simp only [blockM, Matrix.smul_apply, reindex_apply, submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp

theorem one_add_smul_blockM (t : ℝ) (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    1 + t • blockM X₁ X₂ = blockM (1 + t • X₁) (1 + t • X₂) := by
  have h1 : (1 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) = blockM 1 1 := by
    simp [blockM, fromBlocks_one]
  rw [h1, blockM_smul, blockM_add]

theorem lieD_block {F : Sm E (r + s)} (hF : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0)
    (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) (m : GA E r × GA E s) :
    lieD (toL (blockM X₁ X₂)) F.1 (lev (Ad E) r s m) = 0 := by
  set g := lev (Ad E) r s m with hg
  set X : Lie E (r + s) := toL (blockM X₁ X₂) with hX
  let c : ℝ → Lie E (r + s) := fun t => oneL E (r + s) + t • X
  have hc : HasDerivAt c X 0 :=
    (((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E (r + s))).congr_deriv (one_smul ℝ X)
  have h0 : c 0 = oneL E (r + s) := by simp [c]
  have hd : HasFDerivAt (chart F.1 g) (fderiv ℝ (chart F.1 g) (oneL E (r + s))) (c 0) := by
    rw [h0]; exact (differentiableAt_chart F.2 g).hasFDerivAt
  have h2 := hd.comp_hasDerivAt (0 : ℝ) hc
  have ev : ∀ (n : ℕ) (Y : Lie E n), ∀ᶠ t : ℝ in 𝓝 0, oneL E n + t • Y ∈ invSet E n := by
    intro n Y
    have hcont : Continuous fun t : ℝ => oneL E n + t • Y := by fun_prop
    refine hcont.continuousAt.eventually_mem (isOpen_invSet.mem_nhds ?_)
    simp only [zero_smul, add_zero]
    change IsUnit (Matrix.of (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) (Cinf E))))
    rw [Equiv.apply_symm_apply]
    exact isUnit_one
  have hz : (chart F.1 g ∘ c) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ev r (toL X₁), ev s (toL X₂)] with t h1 h2
    obtain ⟨u₁, hu₁⟩ := h1
    obtain ⟨u₂, hu₂⟩ := h2
    have e : c t = toL (lev (Cinf E) r s (u₁, u₂)).val := by
      rw [val_lev]
      change c t = toL (blockM u₁.val u₂.val)
      rw [hu₁, hu₂]
      exact one_add_smul_blockM t X₁ X₂
    rw [Function.comp_apply, e, chart_val, infGL_lev, hg, ← map_mul]
    exact hF _
  exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)


variable (E r s) in
def vanAlg : Subalgebra ℂ (Module.End ℂ (Sm E (r + s))) where
  carrier := {z | ∀ F : Sm E (r + s), (∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
    ∀ m : GA E r × GA E s, (z F).1 (lev (Ad E) r s m) = 0}
  mul_mem' hx hy F hF := hx _ (hy F hF)
  add_mem' {x y} hx hy F hF m := by
    change (x F).1 _ + (y F).1 _ = 0
    rw [hx F hF m, hy F hF m, add_zero]
  algebraMap_mem' c F hF m := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hF m, smul_zero]

theorem Eop_mem_of {a : ℕ} (S : Subalgebra ℂ (Module.End ℂ (Sm E a))) (τ : E →+* ℂ) (p q : Fin a)
    (h : ∀ x, lieS E a p q x ∈ S) : Eop τ p q ∈ S :=
  S.smul_mem (S.sub_mem (h _) (S.smul_mem (h _) _)) _

theorem lie_block_mem (X₁ : Matrix (Fin r) (Fin r) (Cinf E)) (X₂ : Matrix (Fin s) (Fin s) (Cinf E)) :
    lie E (r + s) (toL (blockM X₁ X₂)) ∈ vanAlg E r s :=
  fun _ hF m => lieD_block hF X₁ X₂ m

theorem single_castAdd (i j : Fin r) (x : Cinf E) :
    Matrix.single (Fin.castAdd s i) (Fin.castAdd s j) x = blockM (Matrix.single i j x) (0 : Matrix (Fin s) (Fin s) (Cinf E)) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hc, hc]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem single_natAdd (i j : Fin s) (x : Cinf E) :
    Matrix.single (Fin.natAdd r i) (Fin.natAdd r j) x = blockM (0 : Matrix (Fin r) (Fin r) (Cinf E)) (Matrix.single i j x) := by
  have hc : ∀ k : Fin r, Fin.castAdd s k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl k) := fun k => Fin.ext (by simp)
  have hn : ∀ k : Fin s, Fin.natAdd r k = GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr k) := fun k => Fin.ext (by simp)
  rw [hn, hn]
  ext a b
  obtain ⟨a, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective a
  obtain ⟨b, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective b
  simp only [blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.single_apply]

theorem capR_mem (τ : E →+* ℂ) (u : ℂ) : capR r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_castAdd]; exact lie_block_mem _ _) _

theorem capS_mem (τ : E →+* ℂ) (u : ℂ) : capS r s τ u ∈ vanAlg E r s :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => by
    rw [lieS_apply, single_natAdd]; exact lie_block_mem _ _) _


variable (E) in
def nInvAlg (a r : ℕ) : Subalgebra ℂ (Module.End ℂ (Sm E a)) where
  carrier := {z | ∀ ψ : Sm E a, (∀ (x : BlockIx a r → Ad E) (g : GA E a), ψ.1 (unip x * g) = ψ.1 g) →
    ∀ (x : BlockIx a r → Ad E) (g : GA E a), (z ψ).1 (unip x * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ v g := by
    change (x ψ).1 _ + (y ψ).1 _ = (x ψ).1 _ + (y ψ).1 _
    rw [hx ψ hψ v g, hy ψ hψ v g]
  algebraMap_mem' c ψ hψ v g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ v g]

theorem lie_mem_nInvAlg (a r : ℕ) (X : Lie E a) : lie E a X ∈ nInvAlg E a r := by
  intro ψ hψ v g
  have e : chart ψ.1 (unip v * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ v]
    · rfl
  simp only [GlobalTheory.CuspRep.lie_apply, lieD, e]

theorem cap_mem_nInvAlg (a r : ℕ) (τ : E →+* ℂ) (u : ℂ) : cap (a := a) τ u ∈ nInvAlg E a r :=
  qdet_mem _ _ (fun i j => Eop_mem_of _ τ _ _ fun x => lie_mem_nInvAlg a r _) _

theorem capStable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)) :
    ((∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0) →
      (∀ m : GA E r × GA E s, (capR r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
        ∀ m : GA E r × GA E s, (capS r s τ u F).1 (lev (Ad E) r s m) = 0) ∧
    ((∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)),
        (cap (a := r + s) τ u F).1 (unip x * g) = (cap (a := r + s) τ u F).1 g) :=
  ⟨fun hF => ⟨capR_mem τ u F hF, capS_mem τ u F hF⟩, fun hF => cap_mem_nInvAlg (r + s) r τ u F hF⟩

end GlobalTheory.CompanionTheory.CTFin.CapStable

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterEqOfScalar
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.ScalarUniq

theorem scalarBy_unique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ) (h : Zl.ScalarBy x t c) (h' : Zl.ScalarBy x t c') : c = c' := by
  have hirr : x.rep.IsIrreducible := x.2.rep.irr
  have hnt : Nontrivial x.2.rep.V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne
    refine hab ?_
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have e : c • v = c' • v := (h v).symm.trans (h' v)
  exact smul_left_injective ℂ hv e

end GlobalTheory.CompanionTheory.ScalarUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterTwistPowDegree
section
noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel Matrix

namespace GlobalTheory.CompanionTheory.ScalarTwist

theorem acts_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) {g : G} {c : ℂ}
    (h : ∀ v, ρ g v = c • v) (w : W) : σ g w = c • w := by
  obtain ⟨v, rfl⟩ := φ.toLinearEquiv.surjective w
  show σ g (φ.toIntertwiningMap v) = c • φ.toIntertwiningMap v
  rw [← φ.toIntertwiningMap.isIntertwining, h, map_smul]

theorem scalarBy_nu (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c s : ℂ) (h : Zl.ScalarBy x t c) :
    Zl.ScalarBy (x.nu s) t (c * ((absPow k s t : ℂˣ) : ℂ) ^ x.1) := by
  have hdet : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin x.1) t) = t ^ x.1 := by
    ext; simp [GeneralLinearGroup.scalar]
  refine acts_of_equiv (x.twEquiv (absPow k s) (isSmoothChar_absPow s)) (g := GeneralLinearGroup.scalar (Fin x.1) t) ?_
  intro v
  rw [twist_apply, h v, detChar_apply, hdet, smul_smul]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.ScalarTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminantStatement
section
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_action_determinant : ∀ (n : ℕ) (g : Mat n), g.det ≠ 0 → ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ), (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLin.cone_lin | exact GlobalTheory.CompanionTheory.ConeLin.cone_lin | (intros; apply GlobalTheory.CompanionTheory.ConeLin.cone_lin <;> assumption)
end


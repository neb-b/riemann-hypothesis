module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ResidDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.resid_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G.frame O n), (∀ a : G.G₀, g.p₀ a = 1 → ∀ i, r.chib i a = 1) → ∃ r' : Resid G'.frame O n, Glob.Compat g r r' ∧ ((∀ w, r.Ip w = G.frame.Iu w) → ∀ w, r'.Ip w = G'.frame.Iu w) := by
  intro l _ L G G' g n O _ _ _ r hker
  let c : Fin n → G'.frame.G₀ →* (ResidueField O)ˣ := fun i =>
    g.p₀.liftOfSurjective g.p₀_surj ⟨r.chib i, fun a ha => by
      rw [MonoidHom.mem_ker] at ha ⊢
      exact hker a ha i⟩
  have hca : ∀ i a, c i (g.p₀ a) = r.chib i a := fun i a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hc : ∀ i, (c i).comp g.p₀ = r.chib i := fun i => by
    ext a
    simp only [MonoidHom.comp_apply, hca]
  have hdiag : (diagRep c).comp g.p₀ = diagRep r.chib := by
    ext a
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, hca]
  have hD : (GDet.ofRep (diagRep c)).comap g.p₀ = GDet.ofRep (diagRep r.chib) := by
    rw [(comap_lam n (ResidueField O) _ _ g.p₀ (GDet.ofRep (diagRep c))).2.2.2.2.1 (diagRep c), hdiag]
  have key : ∀ (B : Type) [CommRing B] [Algebra (ResidueField O) B] (z : MonoidAlgebra B G.frame.G₀),
      (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z) =
        (GDet.ofRep (diagRep r.chib)).D B z := by
    intro B _ _ z
    calc (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z)
        = ((GDet.ofRep (diagRep c)).comap g.p₀).D B z := rfl
      _ = (GDet.ofRep (diagRep r.chib)).D B z := by rw [hD]
  let r' : Resid G'.frame O n :=
    { chib := c
      chib_open := fun i => by
        rw [← g.p₀_quot.isOpen_preimage]
        have hset : (g.p₀ ⁻¹' ((c i).ker : Set G'.frame.G₀)) = ((r.chib i).ker : Set G.frame.G₀) := by
          ext a
          simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, hca]
        rw [hset]
        exact r.chib_open i
      chib_inj := fun i j hij => by
        apply r.chib_inj
        rw [← hc i, ← hc j, hij]
      polar := by
        intro B _ _ _ _ y
        obtain ⟨x0, hx0⟩ := Finsupp.mapDomain_surjective (M := B) g.p₀_surj y.coeff
        have hx' : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.ofCoeff x0) = y := by
          rw [MonoidAlgebra.mapDomainRingHom_apply]
          show MonoidAlgebra.ofCoeff (Finsupp.mapDomain _ x0) = y
          rw [hx0]
        rw [← hx', ← (map_star l L G G' g n O B).1 (MonoidAlgebra.ofCoeff x0), key, key]
        exact r.polar B _
      psib := r.psib
      psib_open := r.psib_open
      th := r.th
      th_comm := r.th_comm }
  refine ⟨r', ⟨fun i => (hc i).symm, rfl, rfl⟩, ?_⟩
  intro hIp w
  have hle : ∀ i, G.frame.Iu w ≤ (r.chib i).ker := by
    intro i
    have h1 := hIp w
    unfold Resid.Ip at h1
    exact (inf_eq_left.mp h1).trans (iInf_le _ i)
  unfold Resid.Ip
  apply inf_eq_left.mpr
  rw [le_iInf_iff]
  intro i
  rintro _ ⟨x, hx, rfl⟩
  show c i ((G'.φu w) x) = 1
  rw [← g.p₀_φu w x, hca]
  exact hle i ⟨x, hx, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelDesc
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.sel_desc_fac {l : ℕ} [Fact l.Prime] {L : Loc} {G G' G0 : Glob l L} (g : G.Hom G') (h : G.Hom G0)
    {n : ℕ} {R : Type} [CommRing R] (t : R) (ht : IsNilpotent t) (hl : (l : R) = 0)
    (H : Subgroup G0.Γ) [H.Normal] (ho : IsOpen (H : Set G0.Γ)) (hle : H ≤ G0.η.ker)
    (hk : g.p.ker = PL l (H.comap h.p))
    (ρ : G0.G₀ → Matrix (Fin n) (Fin n) R) (h1 : ρ 1 = 1) (hm : ∀ a b, ρ (a * b) = ρ a * ρ b)
    (hc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ a i j)
    (hu : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, ρ (a ^ l ^ e) = 1)
    (z : G.G₀ → Matrix (Fin n) (Fin n) R) (hzc : ∀ i j, AdicCont (Ideal.span {t}) fun a => z a i j)
    (hz : ∀ a b, z (a * b) = z a + ρ (h.p₀ a) * z b * ρ (h.p₀ a⁻¹)) :
    ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) R, z = fun a => z' (g.p₀ a) := by
  obtain ⟨N, hN⟩ := ht
  have hI : Ideal.span {t} ^ N = ⊥ := by
    rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]
  have hle' : H.comap h.p ≤ G.η.ker := fun a ha => by
    rw [MonoidHom.mem_ker, ← h.η a]
    exact hle ha
  have hmul : ∀ a b : G.G₀, ρ (h.p₀ (a * b)) = ρ (h.p₀ a) * ρ (h.p₀ b) := fun a b => by
    rw [map_mul, hm]
  have hρc : ∀ i j, AdicCont (Ideal.span {t}) fun a => ρ (h.p₀ a) i j := fun i j =>
    (h.adicCont_iff _ (fun c => ρ c i j)).2 (hc i j)
  have hun : ∀ (m : ℕ) (k : G.G₀), (k : G.Γ) ∈ H.comap h.p →
      ∃ e, ∀ i j, (ρ (h.p₀ (k ^ l ^ e)) - 1) i j ∈ Ideal.span {t} ^ m := by
    intro m k hk'
    obtain ⟨e, he⟩ := hu (h.p₀ k) hk'
    exact ⟨e, fun i j => by rw [map_pow, he, sub_self]; exact Submodule.zero_mem _⟩
  have hcoc := (coc_pl l L G n R (Ideal.span {t}) (fun a => ρ (h.p₀ a)) z (H.comap h.p)
    (ho.preimage h.cont) hle' hl (by simp [h1]) hmul hρc hun hzc hz).2
  have hzero : ∀ k : G.G₀, g.p₀ k = 1 → z k = 0 := by
    intro k hk1
    have hmem : (k : G.Γ) ∈ PL l (H.comap h.p) := by
      rw [← hk, MonoidHom.mem_ker]
      exact congrArg Subtype.val hk1
    ext i j
    have hz0 := (hcoc k hmem N i j).2
    rw [hI, Ideal.mem_bot] at hz0
    simpa using hz0
  refine ⟨fun c => z (Classical.choose (g.p₀_surj c)), funext fun a => ?_⟩
  obtain hb' := Classical.choose_spec (g.p₀_surj (g.p₀ a))
  show z a = z (Classical.choose (g.p₀_surj (g.p₀ a)))
  generalize Classical.choose (g.p₀_surj (g.p₀ a)) = b at hb' ⊢
  have hk1 : g.p₀ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hb', inv_mul_cancel]
  have hab : b = a * (a⁻¹ * b) := by group
  rw [hab, hz, hzero _ hk1]
  simp

private theorem UpperTheory.V.Pa.sel_desc_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (m : ℕ)
    (X : Type) [CommRing X] [Algebra x.A X] (hX : algebraMap x.A X (x.t ^ m) = 0) (a : F.G₀)
    (ha : ∀ i j, (mat x.ρ a - 1) i j ∈ Ideal.span {x.t ^ m}) : x.ρX X a = 1 := by
  ext i j
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (ha i j)
  have h0 : algebraMap x.A X ((mat x.ρ a - 1) i j) = 0 := by
    rw [← hc, map_mul, hX, mul_zero]
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  simp only [NP.ρX, Matrix.map_apply]
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem UpperTheory.V.Pa.epM_mul_self_eq_zero (X : Type) [CommRing X] (g n : ℕ)
    (Z : Fin g → Matrix (Fin n) (Fin n) X) : DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  apply DD.ext
  · show (0 : X) * 0 = 0
    simp
  · show (fun r => (0 : X) * Z r c j + Z r i c * 0) = 0
    funext r
    simp
  · show (fun r => (0 : X) * (0 : Fin g → X) r + (0 : Fin g → X) r * 0) = 0
    funext r
    simp
  · show (0 : X) * 0 + 0 * 0 + ∑ r, (Z r i c * (0 : Fin g → X) r + (0 : Fin g → X) r * Z r c j) = 0
    simp

theorem UpperTheory.V.Pa.sel_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' G0 : Glob l L) (g : G.Hom G') (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (H : Subgroup G0.Γ) [H.Normal] (m : ℕ), IsOpen (H : Set G0.Γ) → H ≤ G0.η.ker → x.UnipOn H → g.p.ker = PL l (H.comap h.p) → (∀ z ∈ SelP h x (x.Am m), ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (x.Am m), z = fun a => z' (g.p₀ a)) ∧ ∀ z ∈ Sel1 h (x.Am m) k ∪ Sel2 h (x.Am m) k, ∃ z' : G'.G₀ → Matrix (Fin n) (Fin n) (DD (x.Am m) k.g), z = fun a => z' (g.p₀ a) := by
  intro l _ L G G' G0 g h n x k H _ m ho hle hU hk
  obtain ⟨_, _, hnil1, hnil2, hl0, _⟩ := am_fin l G0.frame n x m k.g
  have hrho := rho_hom l G0.frame n x k (x.Am m)
  have hX0 : algebraMap x.A (x.Am m) (x.t ^ m) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)
  have hl1 : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)) l, hl0, map_zero]
  have hlD : (l : DD (x.Am m) k.g) = 0 := by
    rw [← map_natCast (algebraMap x.A (DD (x.Am m) k.g)) l, hl0, map_zero]
  constructor
  · intro z hz
    obtain ⟨_, hzc, hzm, _⟩ := hz
    refine sel_desc_fac g h (algebraMap x.A (x.Am m) x.t) hnil1 hl1 H ho hle hk (x.ρX (x.Am m))
      hrho.1.1 hrho.1.2.1 hrho.1.2.2 ?_ z hzc hzm
    intro a ha
    obtain ⟨e, he⟩ := hU m a ha
    exact ⟨e, sel_desc_one x m (x.Am m) hX0 _ he⟩
  · have hu2 : ∀ a : G0.G₀, (a : G0.Γ) ∈ H → ∃ e : ℕ, k.ρ1 (x.Am m) (a ^ l ^ e) = 1 := by
      intro a ha
      obtain ⟨e, he⟩ := hU m a ha
      have hX : algebraMap x.A (DD (x.Am m) k.g) (x.t ^ m) = 0 := by
        show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0
        rw [hX0, map_zero]
      have h1 := sel_desc_one x m (DD (x.Am m) k.g) hX _ he
      let φ : G0.G₀ →* Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) :=
        { toFun := k.ρ1 (x.Am m), map_one' := hrho.2.1.1, map_mul' := hrho.2.1.2.1 }
      have hp : ∀ (b : G0.G₀) (N : ℕ), k.ρ1 (x.Am m) (b ^ N) = k.ρ1 (x.Am m) b ^ N :=
        fun b N => map_pow φ b N
      refine ⟨e + 1, ?_⟩
      rw [pow_succ, pow_mul, hp, Kap.ρ1, h1, mul_one]
      have hE := epM_mul_self_eq_zero (x.Am m) k.g n (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m)))
      generalize DD.epM (fun j => (k.κ j (a ^ l ^ e)).map ⇑(algebraMap x.A (x.Am m))) = E at hE ⊢
      have hN : ∀ N : ℕ, (1 + E) ^ N = 1 + N • E := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_zero,
            add_zero, succ_nsmul]
          abel
      rw [hN]
      have hlE : l • E = 0 := Matrix.ext fun i j => by
        rw [Matrix.smul_apply, nsmul_eq_mul, hlD, zero_mul, Matrix.zero_apply]
      rw [hlE, add_zero]
    intro z hz
    rcases hz with hz | hz <;> obtain ⟨_, hzc, hzm, _⟩ := hz <;>
      exact sel_desc_fac g h (algebraMap x.A (DD (x.Am m) k.g) x.t) hnil2 hlD H ho hle hk
        (k.ρ1 (x.Am m)) hrho.2.1.1 hrho.2.1.2.1 hrho.2.1.2.2 hu2 z hzc hzm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelRed
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section

variable {A X X' : Type} [CommRing A] [CommRing X] [Algebra A X] [CommRing X'] [Algebra A X'] (f : X →ₐ[A] X') {n : ℕ}

private theorem map_alg (M : Matrix (Fin n) (Fin n) A) :
    (M.map (algebraMap A X)).map f = M.map (algebraMap A X') := by
  ext i j; simp

private theorem map_mul_alg (M N : Matrix (Fin n) (Fin n) X) : (M * N).map f = M.map f * N.map f :=
  map_mul f.mapMatrix M N

private theorem map_add_one (M : Matrix (Fin n) (Fin n) X) : (1 + M).map f = 1 + M.map f := by
  rw [Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_sub_one (M : Matrix (Fin n) (Fin n) X) : (1 - M).map f = 1 - M.map f := by
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_epM {g : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) A) :
    (DD.epM fun j => (Z j).map (algebraMap A X)).map (DD.map g f) = DD.epM fun j => (Z j).map (algebraMap A X') := by
  ext i j <;> simp [DD.epM, DD.map]

private theorem blk_map (a : ℕ) (V₁ V₂ : Submodule A X) (V₁' V₂' : Submodule A X')
    (h₁ : ∀ y ∈ V₁, f y ∈ V₁') (h₂ : ∀ y ∈ V₂, f y ∈ V₂') :
    ∀ Z ∈ blkMat n a V₁ V₂, Z.map f ∈ blkMat n a V₁' V₂' :=
  fun _ hZ i j => ⟨fun e => h₁ _ ((hZ i j).1 e), fun e => h₂ _ ((hZ i j).2 e)⟩

private theorem part_map (g : ℕ) (b₁ b₂ b₃ b₄ : Bool) :
    ∀ y ∈ ddPart A X g b₁ b₂ b₃ b₄, DD.map g f y ∈ ddPart A X' g b₁ b₂ b₃ b₄ := by
  rintro y ⟨ha, hep, hep', heta⟩
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · show f y.a = 0
    rw [ha hb, map_zero]
  · show (fun j => f (y.ep j)) = 0
    funext j
    rw [hep hb]
    simp
  · show (fun j => f (y.ep' j)) = 0
    funext j
    rw [hep' hb]
    simp
  · show f y.eta = 0
    rw [heta hb, map_zero]

end

theorem UpperTheory.V.Pa.sel_red :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X X' : Type) [CommRing X] [Algebra x.A X] [CommRing X'] [Algebra x.A X'] (f : X →ₐ[x.A] X'), (∀ z ∈ SelP h x X, (fun g => (z g).map f) ∈ SelP h x X') ∧ (∀ z ∈ Sel1 h X k, (fun g => (z g).map (DD.map k.g f)) ∈ Sel1 h X' k) ∧ (∀ z ∈ Sel2 h X k, (fun g => (z g).map (DD.map k.g f)) ∈ Sel2 h X' k) ∧ (∀ g, (k.ρ1 X g).map (DD.map k.g f) = k.ρ1 X' g) ∧ ∀ v, (k.w1 X v).map (DD.map k.g f) = k.w1 X' v ∧ (k.wi1 X v).map (DD.map k.g f) = k.wi1 X' v := by
  intro l _ L G G0 h n x k X X' _ _ _ _ f
  have hρ1 : ∀ g, (k.ρ1 X g).map (DD.map k.g f) = k.ρ1 X' g := by
    intro g
    unfold Kap.ρ1 NP.ρX
    rw [map_mul_alg, map_add_one, map_epM, map_alg]
  have hw1 : ∀ v, (k.w1 X v).map (DD.map k.g f) = k.w1 X' v := by
    intro v
    unfold Kap.w1 NP.wX
    rw [map_mul_alg, map_sub_one, map_epM, map_alg]
  have hwi1 : ∀ v, (k.wi1 X v).map (DD.map k.g f) = k.wi1 X' v := by
    intro v
    unfold Kap.wi1 NP.wiX
    rw [map_mul_alg, map_add_one, map_epM, map_alg]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, hρ1, fun v => ⟨hw1 v, hwi1 v⟩⟩
  · have hV : ∀ Z ∈ Ev x.A X n x.a, Z.map f ∈ Ev x.A X' n x.a :=
      blk_map f x.a ⊤ ⊥ ⊤ ⊥ (fun _ _ => Submodule.mem_top) (fun y hy => by
        rw [Submodule.mem_bot] at hy ⊢
        rw [hy, map_zero])
    have H := (sel_map l G.frame n x.A X X' f x.t (fun g => x.ρX X (h.p₀ g)) (x.wX X) (x.wiX X) _ _ hV z).1 hz
    simp only [NP.ρX, NP.wX, NP.wiX, map_alg] at H
    exact H
  · have hV : ∀ Z ∈ W1 n x.A X k.g x.a, Z.map (DD.map k.g f) ∈ W1 n x.A X' k.g x.a :=
      blk_map (DD.map k.g f) x.a _ _ _ _ (part_map f k.g _ _ _ _) (part_map f k.g _ _ _ _)
    have H := (sel_map l G.frame n x.A (DD X k.g) (DD X' k.g) (DD.map k.g f) x.t
      (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) _ _ hV z).1 hz
    simp only [hρ1, hw1, hwi1] at H
    exact H
  · have hV : ∀ Z ∈ W2 n x.A X k.g x.a, Z.map (DD.map k.g f) ∈ W2 n x.A X' k.g x.a :=
      blk_map (DD.map k.g f) x.a _ _ _ _ (part_map f k.g _ _ _ _) (part_map f k.g _ _ _ _)
    have H := (sel_map l G.frame n x.A (DD X k.g) (DD X' k.g) (DD.map k.g f) x.t
      (fun g => k.ρ1 X (h.p₀ g)) (k.w1 X) (k.wi1 X) _ _ hV z).1 hz
    simp only [hρ1, hw1, hwi1] at H
    exact H
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TwquotEx
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem exists_desc {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (g : G.Hom G')
    (H : OpenNormalSubgroup G.Γ) (hk : g.p.ker ≤ H.toSubgroup) :
    ∃ H' : OpenNormalSubgroup G'.Γ, H'.toSubgroup.comap g.p = H.toSubgroup := by
  have e : (H.toSubgroup.map g.p).comap g.p = H.toSubgroup := Subgroup.comap_map_eq_self hk
  have hq : Topology.IsQuotientMap g.p := g.cont.isClosedMap.isQuotientMap g.cont g.surj
  have ho : IsOpen (H.toSubgroup.map g.p : Set G'.Γ) := by
    rw [← hq.isOpen_preimage, ← Subgroup.coe_comap, e]
    exact H.toOpenSubgroup.isOpen
  exact ⟨{ toSubgroup := H.toSubgroup.map g.p, isOpen' := ho, isNormal' := H.isNormal'.map _ g.surj }, e⟩

theorem UpperTheory.V.Pa.twquot_ex :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), Nonempty (TWQuot T) := by
  intro l _ L G0 T
  haveI hn : T.H.toSubgroup.Normal := T.H.isNormal'
  have ho : IsOpen (T.H.toSubgroup : Set G0.Γ) := T.H.toOpenSubgroup.isOpen
  have hoN : ∀ N, IsOpen (T.H.toSubgroup.comap (T.h N).p : Set (T.GN N).Γ) := fun N => ho.preimage (T.h N).cont
  obtain ⟨G0', g0, ker0⟩ := quot_ex l L G0 T.H.toSubgroup ho (fun a ha => T.H_η a ha) (fun a ha => T.H_ε a ha)
  have hN : ∀ N, ∃ (G' : Glob l L) (g : (T.GN N).Hom G'), g.p.ker = PL l (T.H.toSubgroup.comap (T.h N).p) :=
    fun N => quot_ex l L (T.GN N) _ (hoN N)
      (fun a ha => show (T.GN N).η a = 1 by rw [← (T.h N).η]; exact T.H_η _ ha)
      (fun a ha => by rw [← (T.h N).ε]; exact T.H_ε _ ha)
  choose GN' gN kerN using hN
  have hmap : ∀ N, (gN N).p.ker.map (T.h N).p = g0.p.ker := fun N => by
    rw [kerN, ker0]
    exact pl_map l _ _ (T.h N).p T.H.toSubgroup ho (T.h N).cont (T.h N).surj
  have hd : ∀ N, ∃ h' : (GN' N).Hom G0', ∀ x, h'.p ((gN N).p x) = g0.p ((T.h N).p x) := fun N =>
    hom_desc l L _ _ _ _ (gN N) g0 (T.h N) fun a ha => by
      have : (T.h N).p a ∈ g0.p.ker := hmap N ▸ Subgroup.mem_map_of_mem _ ha
      exact this
  choose h' comm using hd
  obtain ⟨H', hH'⟩ := exists_desc g0 T.H (ker0 ▸ (pl_props l G0.Γ T.H.toSubgroup ho).2.2.1)
  haveI hn' : H'.toSubgroup.Normal := H'.isNormal'
  have ho' : IsOpen (H'.toSubgroup : Set G0'.Γ) := H'.toOpenSubgroup.isOpen
  have hiff : ∀ a, g0.p a ∈ H' ↔ a ∈ T.H := fun a => by
    show a ∈ H'.toSubgroup.comap g0.p ↔ a ∈ T.H.toSubgroup
    rw [hH']
  have hcN : ∀ N, (H'.toSubgroup.comap (h' N).p).comap (gN N).p = T.H.toSubgroup.comap (T.h N).p := fun N => by
    ext a
    show (h' N).p ((gN N).p a) ∈ H' ↔ (T.h N).p a ∈ T.H
    rw [comm, hiff]
  refine ⟨{ G0' := G0', g0 := g0, ker0 := ker0, GN' := GN', gN := gN, kerN := kerN, h' := h', comm := comm
            H' := H', H'_iff := hiff, ph_lim := fun V j => ?_, ker_le := fun N => ?_, fin0 := ?_
            finN := fun N => ?_, pl0 := ?_, plN := fun N => ?_ }⟩
  · let V' : OpenNormalSubgroup G0.Γ :=
      { toOpenSubgroup := V.toOpenSubgroup.comap g0.p g0.cont
        isNormal' := Subgroup.Normal.comap V.isNormal' g0.p }
    refine T.ph_lim V' j fun a ha => ?_
    rw [← ker0, MonoidHom.mem_ker] at ha
    show g0.p a ∈ V.toSubgroup
    rw [ha]; exact one_mem _
  · intro x hx
    obtain ⟨a, rfl⟩ := (gN N).surj x
    have h1 : (T.h N).p a ∈ (gN N).p.ker.map (T.h N).p := by
      rw [hmap, MonoidHom.mem_ker, ← comm]; exact hx
    obtain ⟨b, hb, hba⟩ := h1
    have h2 : a * b⁻¹ ∈ (T.h N).p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hba, mul_inv_cancel]
    have h3 : (gN N).p a = (gN N).p (a * b⁻¹) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.1 hb, inv_one, mul_one]
    rw [h3]
    have h4 : (Subgroup.normalClosure (Set.range fun j => (T.ta N j : (T.GN N).Γ)) ⊔
        PL l (T.H.toSubgroup.comap (T.h N).p)).topologicalClosure ≤
        (Subgroup.normalClosure (Set.range fun j => (gN N).p (T.ta N j))).topologicalClosure.comap (gN N).p := by
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_)
        ((Subgroup.isClosed_topologicalClosure _).preimage (gN N).cont)
      · refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨j, rfl⟩
        exact Subgroup.subset_normalClosure ⟨j, rfl⟩
      · rw [← kerN]; exact MonoidHom.ker_le_comap _ _
    exact h4 (T.ker_le N h2)
  · exact (homl_desc l _ _ g0.p H'.toSubgroup g0.cont g0.surj (hH' ▸ T.fin0)).1
  · have := homl_desc l _ _ (gN N).p (H'.toSubgroup.comap (h' N).p) (gN N).cont (gN N).surj
      (by rw [hcN]; exact (T.finN N).1)
    rw [hcN] at this
    exact ⟨this.1, this.2.trans (T.finN N).2⟩
  · rw [← pl_map l _ _ g0.p H'.toSubgroup ho' g0.cont g0.surj, hH', ← ker0, Subgroup.map_eq_bot_iff]
  · rw [← pl_map l _ _ (gN N).p (H'.toSubgroup.comap (h' N).p) (ho'.preimage (h' N).cont) (gN N).cont (gN N).surj,
      hcN, ← kerN, Subgroup.map_eq_bot_iff]
end


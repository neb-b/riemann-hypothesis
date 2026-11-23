module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContConj
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isUp_mul {A : Type} [CommRing A] {X Y : M4 A} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j hij
  have hB : Matrix.BlockTriangular (X * Y) id :=
    Matrix.BlockTriangular.mul (fun a b h => hX a b h) (fun a b h => hY a b h)
  exact hB hij

private theorem cont_conj {Γ A : Type} [TopologicalSpace Γ] [CommRing A] (I : Ideal A) (f : Γ → M4 A) (x y : M4 A)
    (h : ∀ i j, AdicCont I fun g => f g i j) (i j : Fin 4) : AdicCont I fun g => (x * f g * y) i j := by
  intro N
  have hpi : IsLocallyConstant fun g => fun k m => Ideal.Quotient.mk (I ^ N) (f g k m) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hev : ∀ᶠ g in nhds g0, ∀ k m,
        Ideal.Quotient.mk (I ^ N) (f g k m) = Ideal.Quotient.mk (I ^ N) (f g0 k m) := by
      simp only [Filter.eventually_all]
      intro k m
      exact (h k m N).eventually_eq g0
    filter_upwards [hev] with g hg
    funext k m
    exact hg k m
  convert hpi.comp (fun M : Fin 4 → Fin 4 → A ⧸ I ^ N =>
    ∑ m, ∑ k, Ideal.Quotient.mk (I ^ N) (x i k) * M k m * Ideal.Quotient.mk (I ^ N) (y m j)) using 1
  funext g
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]

theorem UpperTheory.V.Ws.X1.sect :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → (∀ v, Φ.Mu v = ∅) → ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (ν : Γb →* Λˣ) (r : Γb →* M4 R), (∀ g, (ν (π g) : Λ) = a (Φ.ν g)) → r.comp π = P.r → ∀ (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → WLift (Φ.loc π) ν r P.n p → ∃ s : R →ₐ[Λ] A, p.comp s = AlgHom.id Λ R := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hStd hMu Γb _ _ _ _ π hQuo c hRes R _ _ _ P hDef ν r hν hr
    A _ _ _ p hsurj hker hW
  obtain ⟨r', n', hWP, hcont, hr', hn'⟩ := hW
  have hPair := hDef.1.pair
  have hmapmul : ∀ X Y : M4 A, Matrix.map (X * Y) p = Matrix.map X p * Matrix.map Y p := by
    intro X Y
    exact Matrix.map_mul (f := (p : A →+* R))
  have hrπ : ∀ g, Matrix.map (r' (π g)) p = P.r g := by
    intro g
    rw [hr', ← hr]
    rfl
  have hresR : ∀ g i j, res Λ R (P.r g i j) = c.r g i j := by
    intro g i j
    rw [← hDef.1.red, PD.map_r]
    rfl
  have hXunit : ∀ i j, i ≠ j →
      IsUnit (r' (π Φ.g0) i i - r' (π Φ.g0) j j) := by
    intro i j hij
    have hd := hStd.ok.dist i j hij
    have he : res Λ A (r' (π Φ.g0) i i - r' (π Φ.g0) j j) =
        (residue Λ).comp a (Φ.χ i Φ.g0) - (residue Λ).comp a (Φ.χ j Φ.g0) := by
      rw [← res_map p, map_sub]
      have hi : p (r' (π Φ.g0) i i) = P.r Φ.g0 i i := by
        rw [← hrπ]
        rfl
      have hj : p (r' (π Φ.g0) j j) = P.r Φ.g0 j j := by
        rw [← hrπ]
        rfl
      rw [hi, hj, map_sub, hresR, hresR, hRes.res.diag, hRes.res.diag]
    by_contra hnu
    have hm : r' (π Φ.g0) i i - r' (π Φ.g0) j j ∈ maximalIdeal A := (mem_maximalIdeal _).2 hnu
    rw [← res_eq_zero_iff Λ A, he] at hm
    rw [hm] at hd
    exact not_isUnit_zero hd
  obtain ⟨u, hu1, hup, hudiag⟩ := X1.diagLift p hsurj hker (algebraMap Λ A (ν (π Φ.g0)))
    (r' (π Φ.g0)) ((ν (π Φ.g0)).isUnit.map (algebraMap Λ A)) (hWP.mult (π Φ.g0))
    (by rw [hrπ]; exact hPair.nrm) hXunit
  have huadj : adj u * u = 1 := by
    have h := hu1
    unfold IsGSp at h
    simpa using h
  have hu_adj : u * adj u = 1 := mul_eq_one_comm.1 huadj
  have hadjGSp : IsGSp 1 (adj u) := by
    unfold IsGSp
    rw [(grp A).2.1 u, hu_adj, one_smul]
  have hmapadj : Matrix.map (adj u) p = 1 := by
    have h := (grp A).2.2.2.2.2.1 R (p : A →+* R) u
    have h' : Matrix.map (adj u) p = adj (Matrix.map u p) := h.symm
    rw [h', hup, (grp R).2.2.2.2.1]
  have hlow : ∀ v, ∃ m b, IsLow m ∧ IsGSp 1 b ∧ IsUp b ∧ IsUp (adj b) ∧
      Matrix.map m p = Matrix.map (adj u * n' v) p ∧ m = adj u * n' v * b := by
    intro v
    refine X1.lowLift p hsurj hker (adj u * n' v) ?_ ?_
    · have h := (grp A).2.2.2.2.2.2.2.1 1 1 (adj u) (n' v) hadjGSp (hWP.sp v)
      simpa using h
    · rw [hmapmul, hmapadj, one_mul, hn']
      exact hPair.low v
  choose m b hm using hlow
  let r'' : Γ →* M4 A :=
    { toFun := fun g => adj u * r' (π g) * u
      map_one' := by simp [huadj]
      map_mul' := by
        intro x y
        simp only [map_mul]
        calc adj u * (r' (π x) * r' (π y)) * u
            = adj u * r' (π x) * (u * adj u) * r' (π y) * u := by rw [hu_adj]; noncomm_ring
          _ = adj u * r' (π x) * u * (adj u * r' (π y) * u) := by noncomm_ring }
  let P' : PD Φ.ι Γ A := ⟨r'', m⟩
  have hPP' : P'.map (p : A →+* R) = P := by
    apply PD.ext
    · apply MonoidHom.ext
      intro g
      rw [PD.map_r]
      change Matrix.map (adj u * r' (π g) * u) p = P.r g
      rw [hmapmul, hmapmul, hmapadj, hup, hrπ, one_mul, mul_one]
    · funext v
      change Matrix.map (m v) p = P.n v
      rw [(hm v).2.2.2.2.1, hmapmul, hmapadj, one_mul, hn']
  have hLift : Φ.Lifts a c P' := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g
      change IsGSp (algebraMap Λ A (a (Φ.ν g))) (adj u * r' (π g) * u)
      rw [← hν g]
      have h1 : IsGSp (algebraMap Λ A (ν (π g))) (r' (π g)) := hWP.mult (π g)
      have h2 := (grp A).2.2.2.2.2.2.2.1 _ _ _ _ ((grp A).2.2.2.2.2.2.2.1 _ _ _ _ hadjGSp h1) hu1
      simpa using h2
    · intro g hg
      have hπg : π g = 1 := by
        rw [← MonoidHom.mem_ker, hQuo.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)
      change adj u * r' (π g) * u = 1
      rw [hπg, map_one, mul_one, huadj]
    · exact hudiag
    · intro v
      exact (hm v).1
    · intro v s hs
      change IsUp (adj (m v) * (adj u * r' (π s) * u) * m v)
      have hfl : IsUp (adj (n' v) * r' (π s) * n' v) := hWP.flag v ⟨s, hs⟩
      have key : adj (m v) * (adj u * r' (π s) * u) * m v =
          adj (b v) * (adj (n' v) * r' (π s) * n' v) * b v := by
        rw [(hm v).2.2.2.2.2]
        simp only [(grp A).1, (grp A).2.1]
        calc adj (b v) * (adj (n' v) * u) * (adj u * r' (π s) * u) * (adj u * n' v * b v)
            = adj (b v) * adj (n' v) * (u * adj u) * r' (π s) * (u * adj u) * n' v * b v := by
              noncomm_ring
          _ = adj (b v) * (adj (n' v) * r' (π s) * n' v) * b v := by
              rw [hu_adj]
              noncomm_ring
      rw [key]
      exact isUp_mul (isUp_mul (hm v).2.2.2.1 hfl) (hm v).2.2.1
    · intro v s hs
      rw [hMu v] at hs
      exact absurd hs (Set.notMem_empty _)
    · intro i j
      exact cont_conj (maximalIdeal A) (fun g => r' (π g)) (adj u) u
        (fun i j N => (hcont i j N).comp_continuous hQuo.cont) i j
    · have hres : (res Λ A : A →+* ResidueField Λ) = (res Λ R : R →+* ResidueField Λ).comp (p : A →+* R) := by
        ext x
        exact (res_map p x).symm
      rw [hres, ← PD.map_map, hPP', hDef.1.red]
  obtain ⟨f, hf, -⟩ := hDef.2 A P' hLift
  obtain ⟨g0, -, huniq⟩ := hDef.2 R P hDef.1
  refine ⟨f, ?_⟩
  have e1 : p.comp f = g0 := by
    apply huniq
    change P.map ((p : A →+* R).comp (f : R →+* A)) = P
    rw [← PD.map_map, hf, hPP']
  have e2 : AlgHom.id Λ R = g0 := by
    apply huniq
    apply PD.ext
    · apply MonoidHom.ext
      intro g
      rw [PD.map_r]
      ext i j
      rfl
    · funext v
      ext i j
      rfl
  rw [e1, e2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GspLift
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_mat {S Q : Type} [TopologicalSpace S] {f : S → M4 Q}
    (h : ∀ i j, IsLocallyConstant fun s => f s i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ᶠ t in nhds s, ∀ i j, f t i j = f s i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq s
  exact this.mono fun t ht => Matrix.ext ht

private def corr {A : Type} [CommRing A] (c n : A) (y : M4 A) : M4 A := y * (1 - c • (adj y * y - n • 1))

private theorem corr_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c n : A) (y : M4 A) :
    (corr c n y).map f = corr (f c) (f n) (y.map f) := by
  obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
  rw [corr, corr, hm, ← Matrix.map_mul, Matrix.map_mul]
  generalize adj y * y = w
  congr 1
  ext i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem corr_gsp {A : Type} [CommRing A] (c n : A) (y : M4 A) (hc : 2 * c * n = 1)
    (hE : (adj y * y - n • 1) * (adj y * y - n • 1) = 0) : IsGSp n (corr c n y) := by
  obtain ⟨hmul, hadj, hadd, hsm, h1, -⟩ := grp A
  unfold IsGSp corr
  obtain ⟨E, hE'⟩ : ∃ E, E = adj y * y - n • 1 := ⟨_, rfl⟩
  have a1 : adj E = E := by
    rw [hE', sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, hmul, hadj]
  have a2 : adj y * y = E + n • 1 := by rw [hE', sub_add_cancel]
  rw [← hE'] at hE ⊢
  have a3 : adj (1 - c • E) = 1 - c • E := by
    rw [sub_eq_add_neg, ← neg_smul, hadd, hsm, h1, a1]
  rw [hmul, a3, mul_assoc, ← mul_assoc (adj y), a2]
  simp only [mul_sub, sub_mul, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, hE, one_mul, mul_one, smul_zero,
    smul_add, smul_sub, smul_smul, zero_add, sub_zero]
  have : E = (2 * c * n) • E := by rw [hc, one_smul]
  linear_combination (norm := module) this

private theorem up_mul {A : Type} [CommRing A] {X Y : M4 A} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k < i
  · rw [hX i k e, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 e)), mul_zero]

private theorem corr_up {A : Type} [CommRing A] (c n : A) {y : M4 A} (hy : IsUp y) : IsUp (corr c n y) := by
  have a : IsUp (adj y) := fun i j h => by
    rw [adj_apply, hy _ _ (Fin.rev_lt_rev.2 h), smul_zero]
  refine up_mul hy fun i j h => ?_
  simp [up_mul a hy i j h, Matrix.one_apply_ne h.ne']

theorem UpperTheory.V.Ws.X1.gspLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (S : Type) [TopologicalSpace S] (ν : S → Λˣ) (x : S → M4 R), AdicCont (maximalIdeal Λ) (fun s => (ν s : Λ)) → (∀ i j, AdicCont (maximalIdeal R) fun s => x s i j) → (∀ s, IsGSp (algebraMap Λ R (ν s)) (x s)) → ∃ y : S → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧ (∀ s, IsGSp (algebraMap Λ A (ν s)) (y s)) ∧ (∀ s, (y s).map p = x s) ∧ ((∀ s, IsUp (x s)) → ∀ s, IsUp (y s)) := by
  intro Λ _ _ _ _ h2 A R _ _ _ _ _ _ p hp hs S _ ν x hν hx hg
  classical
  choose z z1 z2 using fun i j => (UpperTheory.V.Ws.X1.contLift p hp hs).1 S (fun s => x s i j) (hx i j)
  let y0 : S → M4 A := fun s => Matrix.of fun i j => if ∀ t, x t i j = 0 then 0 else z i j s
  have b0 : ∀ i j, AdicCont (maximalIdeal A) fun s => y0 s i j := fun i j => by
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.of_apply, if_pos e]
      exact fun _ => IsLocallyConstant.const _
    · simp only [y0, Matrix.of_apply, if_neg e]
      exact z1 i j
  have b1 : ∀ s, (y0 s).map p = x s := fun s => by
    ext i j
    by_cases e : ∀ t, x t i j = 0
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_pos e, map_zero, e s]
    · simp only [y0, Matrix.map_apply, Matrix.of_apply, if_neg e, z2]
  obtain ⟨u, hu⟩ := h2.exists_right_inv
  have hk : ∀ a b : A, p a = 0 → p b = 0 → a * b = 0 := fun a b ha hb => by
    have ha' : a ∈ maximalIdeal A := fun h => by
      have := h.map p
      rw [ha] at this
      exact not_isUnit_zero this
    have : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul ha' hb
    rwa [hs, Ideal.mem_bot] at this
  have hE : ∀ s i j, p ((adj (y0 s) * y0 s - algebraMap Λ A (ν s) • (1 : M4 A)) i j) = 0 := fun s i j => by
    obtain ⟨-, -, -, -, -, hm, -⟩ := grp A
    have e1 : (adj (y0 s) * y0 s).map p = algebraMap Λ R (ν s) • (1 : M4 R) := by
      have := hm R (p : A →+* R) (y0 s)
      simp only [RingHom.coe_coe] at this
      rw [Matrix.map_mul, ← this, b1]
      exact hg s
    have e2 := congrFun (congrFun e1 i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.sub_apply, map_sub, e2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  refine ⟨fun s => corr (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s), fun i j N => ?_,
    fun s => corr_gsp _ _ _ ?_ ?_, fun s => ?_, fun h s => corr_up _ _ fun i j e => ?_⟩
  · let q := Ideal.Quotient.mk (maximalIdeal A ^ N)
    have c1 : IsLocallyConstant fun s => (y0 s).map q := lc_mat fun i j => b0 i j N
    have c2 : IsLocallyConstant fun s => q (algebraMap Λ A (ν s)) := by
      have hle : maximalIdeal Λ ^ N ≤ (maximalIdeal A ^ N).comap (algebraMap Λ A) :=
        (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.1 (map_maximalIdeal_le (algebraMap Λ A))) N).trans
          (Ideal.le_comap_pow _ N)
      exact (hν N).comp (Ideal.quotientMap _ _ hle)
    have c3 : ∀ s, q (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) =
        q (algebraMap Λ A u) * Ring.inverse (q (algebraMap Λ A (ν s))) := fun s => by
      rw [map_mul, map_mul]
      congr 1
      exact (Ring.inverse_unit (Units.map (q.comp (algebraMap Λ A)).toMonoidHom (ν s))).symm
    have c4 := (c1.prodMk c2).comp fun w => corr (q (algebraMap Λ A u) * Ring.inverse w.2) w.2 w.1 i j
    convert c4 using 2 with s
    simp only [Function.comp_apply]
    rw [← c3, ← corr_map]
    rfl
  · rw [← map_ofNat (algebraMap Λ A) 2, ← map_mul, ← map_mul, ← mul_assoc, hu, one_mul, Units.inv_mul, map_one]
  · ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hk _ _ (hE s i k) (hE s k j)
  · have := corr_map (p : A →+* R) (algebraMap Λ A (u * ((ν s)⁻¹ : Λˣ))) (algebraMap Λ A (ν s)) (y0 s)
    simp only [RingHom.coe_coe] at this
    have g := hg s
    unfold IsGSp at g
    rw [this, b1, corr, g, p.commutes (ν s), sub_self, smul_zero, sub_zero, mul_one]
  · simp only [y0, Matrix.of_apply, if_pos fun t => h t i j e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuQuot
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at hp
  · exact h.cont.map _ (fun x hx =>
      (res_eq_zero_iff Λ R' _).mp ((res_map f x).trans ((res_eq_zero_iff Λ R x).mpr hx)))
  · rw [PD.map_map]
    convert h.red using 2
    exact RingHom.ext fun x => res_map f x

private theorem lifts_noMu {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) : Φ.noMu.Lifts a c P :=
  ⟨⟨h.pair.mult, h.pair.kill, h.pair.nrm, h.pair.low, h.pair.flag, fun _ _ hs => hs.elim⟩, h.cont, h.red⟩

theorem UpperTheory.V.Ws.X1.muQuot :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (P' : PD Φ.ι Γ R'), Φ.noMu.IsDef a c P' → ∃ (g : R' →ₐ[Λ] R) (e : Φ.ι × Fin 2 → R'), Function.Surjective g ∧ RingHom.ker g = Ideal.span (Set.range e) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd c hres ζ hζ hν R _ _ _ P hP R' _ _ _ P' hP'
  obtain ⟨g, hg, -⟩ := hP'.2 R P (lifts_noMu hP.1)
  have hPψ := (X1.muIff Φ l a hstd c hres ζ hζ hν R P (lifts_noMu hP.1)).mp hP.1
  let e : Φ.ι × Fin 2 → R' := fun p => P'.ψ p.1 (Fin.castLE (by norm_num) p.2) (ζ p.1) - 1
  let I : Ideal R' := Ideal.span (Set.range e)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨v, i⟩, rfl⟩
      have key : ∀ j : Fin 4, g (P'.ψ v j (ζ v)) = P.ψ v j (ζ v) := by
        intro j
        rw [← hg, PD.map_ψ]
        rfl
      fin_cases i
      · simp [e, key, (hPψ v).1]
      · simp [e, key, (hPψ v).2]
    · exact map_zero g
    · intro x y _ _ hx hy
      rw [map_add (f := _), hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 := hIg 1 (htop ▸ Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (R' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let π : R' →ₐ[Λ] R' ⧸ I := Ideal.Quotient.mkₐ Λ I
  haveI : IsCO Λ (R' ⧸ I) := co_quot Λ R' (R' ⧸ I) π (Ideal.Quotient.mkₐ_surjective Λ I)
  have hQn : Φ.noMu.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := lifts_map hP'.1 π
  have hQ : Φ.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := by
    refine (X1.muIff Φ l a hstd c hres ζ hζ hν (R' ⧸ I) _ hQn).mpr (fun v => ⟨?_, ?_⟩)
    · rw [PD.map_ψ]
      have hm : e (v, 0) ∈ I := Ideal.subset_span ⟨(v, 0), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
    · rw [PD.map_ψ]
      have hm : e (v, 1) ∈ I := Ideal.subset_span ⟨(v, 1), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
  obtain ⟨h, hh, -⟩ := hP.2 (R' ⧸ I) _ hQ
  obtain ⟨π', -, huniq⟩ := hP'.2 (R' ⧸ I) _ hQn
  have hhg : h.comp g = π := by
    rw [huniq (h.comp g) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hg, hh]),
      huniq π rfl]
  let gb : R' ⧸ I →ₐ[Λ] R := Ideal.Quotient.liftₐ I g hIg
  obtain ⟨i0, -, huniqP⟩ := hP.2 R P hP.1
  have hgb : gb.comp π = g := by
    ext x
    rfl
  have hid : gb.comp h = AlgHom.id Λ R := by
    rw [huniqP (gb.comp h) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hh, PD.map_map,
        ← AlgHom.comp_toRingHom, hgb, hg]),
      huniqP (AlgHom.id Λ R) (by beta_reduce; rw [← hg, PD.map_map]; rfl)]
  refine ⟨g, e, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective Λ I (h y)
    refine ⟨z, ?_⟩
    have hy := congrArg (fun f : R →ₐ[Λ] R => f y) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hy
    rw [← hz] at hy
    exact hy
  · apply le_antisymm
    · intro x hx
      have hx' : π x = 0 := by
        rw [← hhg, AlgHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hx'
    · intro x hx
      exact RingHom.mem_ker.mpr (hIg x hx)
end


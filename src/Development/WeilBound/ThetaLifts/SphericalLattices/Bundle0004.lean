module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.FunAvg
section
noncomputable section

namespace PositivityTheory.Sph

section AvgAbs

variable {Γ : Type} [Group Γ]

def avgQ (H : Subgroup Γ) (f : Γ → ℂ) : ℂ := (H.index : ℂ)⁻¹ * ∑ᶠ q : Γ ⧸ H, f (Quotient.out q)

theorem out_mk_inv {H : Subgroup Γ} {f : Γ → ℂ} (hf : ∀ x, ∀ h ∈ H, f (x * h) = f x) (g : Γ) :
    f (Quotient.out (g : Γ ⧸ H)) = f g := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [e, hf g h h.2]

theorem avgQ_le {H H' : Subgroup Γ} (hle : H' ≤ H) (h0 : H'.index ≠ 0) {f : Γ → ℂ}
    (hf : ∀ x, ∀ h ∈ H, f (x * h) = f x) : avgQ H' f = avgQ H f := by
  classical
  have hH0 : H.index ≠ 0 := ne_zero_of_dvd_ne_zero h0 (Subgroup.index_dvd_of_le hle)
  have hmul := Subgroup.relIndex_mul_index hle
  have hR0 : H'.relIndex H ≠ 0 := fun h => h0 (by rw [← hmul, h, zero_mul])
  have : Finite (Γ ⧸ H') := Subgroup.index_ne_zero_iff_finite.1 h0
  have : Finite (Γ ⧸ H) := Subgroup.index_ne_zero_iff_finite.1 hH0
  have : Finite (H ⧸ H'.subgroupOf H) := Subgroup.index_ne_zero_iff_finite.1 hR0
  let _ := Fintype.ofFinite (Γ ⧸ H')
  let _ := Fintype.ofFinite (Γ ⧸ H)
  let _ := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  have hf' : ∀ x, ∀ h ∈ H', f (x * h) = f x := fun x h hh => hf x h (hle hh)
  have hg : ∀ q' : Γ ⧸ H', f (Quotient.out q') = f (Quotient.out ((Subgroup.quotientEquivProdOfLE hle q').1)) := fun q' => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q'
    have e : ((Subgroup.quotientEquivProdOfLE hle (g : Γ ⧸ H')).1 : Γ ⧸ H) = (g : Γ ⧸ H) := rfl
    rw [e, out_mk_inv hf', out_mk_inv hf]
  have hcard : (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) = (H'.relIndex H : ℂ) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  unfold avgQ
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    Fintype.sum_equiv (Subgroup.quotientEquivProdOfLE hle) _ (fun p => f (Quotient.out p.1)) hg, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [← Finset.mul_sum, ← hmul, Nat.cast_mul]
  have a : (H'.relIndex H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hR0
  have b : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hH0
  field_simp

theorem avgQ_mul {N : Subgroup Γ} [N.Normal] {f : Γ → ℂ} (hf : ∀ x, ∀ h ∈ N, f (x * h) = f x) (k : Γ) :
    avgQ N (fun x => f (x * k)) = avgQ N f := by
  unfold avgQ
  congr 1
  have e : ∀ q : Γ ⧸ N, f (Quotient.out q * k) = f (Quotient.out (q * (k : Γ ⧸ N))) := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q, ← QuotientGroup.mk_mul]
    rw [out_mk_inv hf]
  simp only [e]
  exact finsum_comp_equiv (Equiv.mulRight (k : Γ ⧸ N)) (f := fun q => f (Quotient.out q))

theorem avgQ_add {H : Subgroup Γ} (h0 : H.index ≠ 0) (f g : Γ → ℂ) :
    avgQ H (fun x => f x + g x) = avgQ H f + avgQ H g := by
  have : Finite (Γ ⧸ H) := Subgroup.index_ne_zero_iff_finite.1 h0
  unfold avgQ
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _), mul_add]

theorem avgQ_smul (H : Subgroup Γ) (c : ℂ) (f : Γ → ℂ) : avgQ H (fun x => c * f x) = c * avgQ H f := by
  unfold avgQ
  rw [← mul_finsum, mul_left_comm]

end AvgAbs

theorem avgSt : AvgSt := by
  classical
  intro G S _ _ _ K V ω l₀ hV h1 hmul hst
  let f : S → K → ℂ := fun φ x => l₀ (ω x φ)
  have hfe : ∀ φ (x : K), f φ x = l₀ (ω x φ) := fun _ _ => rfl
  have hinvH : ∀ φ ∈ V, ∀ H : Subgroup G, (∀ k ∈ H, ω k φ = φ) → ∀ (x : K), ∀ h ∈ H.subgroupOf K, f φ (x * h) = f φ x :=
    fun φ hφ H hH x h hh => by
      rw [hfe, hfe, Subgroup.coe_mul, hmul x x.2 h h.2 φ hφ, hH h (Subgroup.mem_subgroupOf.1 hh)]
  choose Hc hHcK hHc0 hHcfix using hst
  have fin1 : ∀ φ (hφ : φ ∈ V), ((Hc φ hφ).subgroupOf K).FiniteIndex := fun φ hφ => ⟨hHc0 φ hφ⟩
  let N : ∀ φ, φ ∈ V → Subgroup K := fun φ hφ => ((Hc φ hφ).subgroupOf K).normalCore
  have hNn : ∀ φ hφ, (N φ hφ).Normal := fun φ hφ => Subgroup.normalCore_normal _
  have hN0 : ∀ φ hφ, (N φ hφ).index ≠ 0 := fun φ hφ => by
    haveI := fin1 φ hφ
    exact (Subgroup.finiteIndex_normalCore _).index_ne_zero
  have hNinv : ∀ φ hφ, ∀ (x : K), ∀ h ∈ N φ hφ, f φ (x * h) = f φ x := fun φ hφ x h hh =>
    hinvH φ hφ _ (hHcfix φ hφ) x h (Subgroup.normalCore_le _ hh)

  have key : ∀ φ (hφ : φ ∈ V) (H' : Subgroup K), H'.index ≠ 0 → (∀ (x : K), ∀ h ∈ H', f φ (x * h) = f φ x) →
      avgQ H' (f φ) = avgQ (N φ hφ) (f φ) := fun φ hφ H' h0 hH' => by
    have hM := Subgroup.index_inf_ne_zero h0 (hN0 φ hφ)
    rw [← avgQ_le inf_le_left hM hH', avgQ_le inf_le_right hM (hNinv φ hφ)]
  let lamF : S → ℂ := fun φ => if hφ : φ ∈ V then avgQ (N φ hφ) (f φ) else 0
  have hlamF : ∀ φ (hφ : φ ∈ V), lamF φ = avgQ (N φ hφ) (f φ) := fun φ hφ => dif_pos hφ
  let lamV : V →ₗ[ℂ] ℂ :=
    { toFun := fun φ => lamF φ
      map_add' := fun φ ψ => by
        have hφ := φ.2
        have hψ := ψ.2
        have hs := V.add_mem hφ hψ
        have h0 := Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)
        change lamF (φ.1 + ψ.1) = lamF φ.1 + lamF ψ.1
        have e : f (φ.1 + ψ.1) = fun x => f φ.1 x + f ψ.1 x := funext fun x => by rw [hfe, hfe, hfe, map_add (f := _), map_add (f := _)]
        rw [hlamF _ hs, hlamF _ hφ, hlamF _ hψ, ← key _ hs _ h0 (fun x h hh => by
            rw [e]; exact congrArg₂ (· + ·) (hNinv _ hφ x h hh.1) (hNinv _ hψ x h hh.2)),
          ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2), e,
          avgQ_add h0]
      map_smul' := fun c φ => by
        have hφ := φ.2
        have hs := V.smul_mem c hφ
        change lamF (c • φ.1) = c • lamF φ.1
        have e : f (c • φ.1) = fun x => c * f φ.1 x := funext fun x => by rw [hfe, hfe, map_smul, map_smul, smul_eq_mul]
        rw [hlamF _ hs, hlamF _ hφ, ← key _ hs _ (hN0 _ hφ) (fun x h hh => by rw [e]; exact congrArg (c * ·) (hNinv _ hφ x h hh)),
          e, avgQ_smul, smul_eq_mul] }
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective V.subtype V.ker_subtype
  have hπ' : ∀ φ (hφ : φ ∈ V), π φ = ⟨φ, hφ⟩ := fun φ hφ => LinearMap.congr_fun hπ ⟨φ, hφ⟩
  have hlam : ∀ φ (hφ : φ ∈ V), (lamV ∘ₗ π) φ = avgQ (N φ hφ) (f φ) := fun φ hφ => by
    rw [LinearMap.comp_apply, hπ' φ hφ]
    exact hlamF φ hφ
  refine ⟨lamV ∘ₗ π, fun k hk φ hφ => ?_, fun φ hφ H hHK hH0 hH => ?_⟩
  · have hψ := hV k hk φ hφ
    haveI := hNn φ hφ
    haveI := hNn _ hψ
    have h0 := Subgroup.index_inf_ne_zero (hN0 _ hφ) (hN0 _ hψ)
    have e : f (ω k φ) = fun x => f φ (x * ⟨k, hk⟩) := funext fun x => by
      rw [hfe, hfe, Subgroup.coe_mul, hmul x x.2 k hk φ hφ]
    rw [hlam _ hψ, hlam _ hφ, ← key _ hψ _ h0 (fun x h hh => hNinv _ hψ x h hh.2),
      ← key _ hφ _ h0 (fun x h hh => hNinv _ hφ x h hh.1), e]
    exact avgQ_mul (N := N φ hφ ⊓ N (ω k φ) hψ) (fun x h hh => hNinv _ hφ x h hh.1) _
  · rw [hlam φ hφ, ← key φ hφ (H.subgroupOf K) hH0 (hinvH φ hφ H hH)]
    rfl

end PositivityTheory.Sph

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.FunFin
section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK

theorem finSt_relIndex_le {G : Type} [Group G] {H K L : Subgroup G} (hKL : K ≤ L) (h : H.relIndex L ≠ 0) :
    H.relIndex K ≠ 0 := by
  have : (H.subgroupOf L).FiniteIndex := ⟨h⟩
  have : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKL).injective
  exact Subgroup.index_ne_zero_of_finite

theorem finSt_relIndex_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem finSt_KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (b : GL (Fin n) (w.adicCompletion E)) :
    (KGL w (n := n) ⊓ (KGL w (n := n)).map (MulAut.conj b).toMonoidHom).relIndex (KGL w (n := n)) ≠ 0 := by
  obtain ⟨ho, hc⟩ := SatCompare.isOpen_isCompact_KGL w n
  have hcont : Continuous fun x : GL (Fin n) (w.adicCompletion E) => b⁻¹ * x * b :=
    (continuous_const.mul continuous_id).mul continuous_const
  refine finSt_relIndex_nhds hc (U := (KGL w (n := n) : Set _) ∩ (fun x => b⁻¹ * x * b) ⁻¹' (KGL w (n := n) : Set _))
    ((ho.inter (ho.preimage hcont)).mem_nhds ⟨one_mem _, by simp [one_mem]⟩) fun k _ hk => ⟨hk.1, ?_⟩
  refine ⟨b⁻¹ * k * b, hk.2, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

theorem finSt : FinSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw g hg
  classical
  have hv : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hv
  obtain ⟨a, ha, -⟩ := PositivityTheory.ThKH.Iwas.exists_frame hB.cm hw hv hc hW
  let Φ : UA σ W.J →* GL (Fin d) (w.adicCompletion E) :=
    (MulAut.conj a⁻¹).toMonoidHom.comp
      ((Units.map (RingHom.mapMatrix (PositivityTheory.ThKH.Iwas.piE hv)).toMonoidHom).comp (Subgroup.subtype _))
  have hΦ : ∀ x, ((Φ x : GL (Fin d) (w.adicCompletion E)) : Matrix (Fin d) (Fin d) (w.adicCompletion E)) =
      (a⁻¹).1 * (mat x).map (PositivityTheory.ThKH.Iwas.piE hv) * a.1 := fun x => by
    simp [Φ, mat]
  have memK : ∀ x ∈ UAt σ W (evFin F v), x ∈ KSub σ W v ↔ Φ x ∈ KGL w (n := d) := fun x hx => by
    rw [mem_GLint_iff, ← map_inv, hΦ, hΦ]
    change (x ∈ UAt σ W (evFin F v) ∧ ∀ y ∈ latW W v, mat x *ᵥ y ∈ latW W v ∧ mat x⁻¹ *ᵥ y ∈ latW W v) ↔ _
    rw [← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha, ← PositivityTheory.ThKH.Iwas.stab_iff hw hv ha]
    exact ⟨fun H => ⟨fun y hy => (H.2 y hy).1, fun y hy => (H.2 y hy).2⟩, fun H => ⟨hx, fun y hy => ⟨H.1 y hy, H.2 y hy⟩⟩⟩
  set K := KSub σ W v
  set H' := KGL w (n := d) ⊓ (KGL w (n := d)).map (MulAut.conj (Φ g)).toMonoidHom
  have h1 : (H'.comap Φ).relIndex K ≠ 0 := by
    rw [Subgroup.relIndex_comap]
    refine finSt_relIndex_le ?_ (finSt_KGL w d (Φ g))
    rintro _ ⟨k, hk, rfl⟩
    exact (memK k hk.1).1 hk
  have h2 : H'.comap Φ ⊓ K ≤ conjInf K g := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨hk2, g⁻¹ * k * g, ?_, ?_⟩
    · have hx : g⁻¹ * k * g ∈ UAt σ W (evFin F v) := mul_mem_UAt (mul_mem_UAt (inv_mem_UAt hg) hk2.1) hg
      refine (memK _ hx).2 ?_
      obtain ⟨y, hy, ey⟩ := hk1.2
      have : Φ (g⁻¹ * k * g) = y := by
        rw [map_mul, map_mul, map_inv, ← ey]
        simp [MulAut.conj_apply, mul_assoc]
      rw [this]; exact hy
    · simp [MulAut.conj_apply, mul_assoc]
  have h3 : (H'.comap Φ ⊓ K).relIndex K ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
  intro h0
  exact h3 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K h2))

end PositivityTheory.Sph

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.InvMemKgKCart2
section
noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Abstract

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_map_cart2 (n : ℕ) : (antiJ L n).map c = antiJ L n := by
  ext i j
  simp only [Matrix.map_apply, antiJ]
  split_ifs <;> simp

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem iso_cT_cart2 (hc : ∀ x, c (c x) = x) {n : ℕ} (M : Matrix (Fin n) (Fin n) L) :
    Iso c (antiJ L n) (antiJ L n) M ↔ cT c M * antiJ L n * M = antiJ L n := by
  have hcc : ∀ N : Matrix (Fin n) (Fin n) L, (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  constructor
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, antiJ_map_cart2, hcc] at this
    exact this
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, antiJ_map_cart2] at this
    rw [cT, Matrix.transpose_map, hcc] at this
    exact this

theorem inv_mem_KgK_cart2 {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {n : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin n) (Fin n) L) (hiso : ∀ g, Iso c (antiJ L n) (antiJ L n) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (antiJ L n) (antiJ L n) M → ∃ g ∈ U, Φ g = M) (K : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1) :
    ∀ h ∈ U, ∃ k₁ ∈ K, ∃ k₂ ∈ K, h⁻¹ = k₁ * h * k₂ := by
  have hcc : ∀ x, c (c x) = x := hU.1
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _ (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  have hherm : ∀ i j, c ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp
  intro h hh
  let g : GL (Fin n) L := Φ.toHomUnits h
  have eg : ∀ x : G, ((Φ.toHomUnits x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Φ x := fun _ => rfl
  have hg : g ∈ UJ c (J : Matrix (Fin n) (Fin n) L) := by
    show cT c (g : Matrix (Fin n) (Fin n) L) * _ * (g : Matrix (Fin n) (Fin n) L) = _
    rw [hJe, eg]
    exact (iso_cT_cart2 hcc _).1 (hiso h)
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ hherm hg
  have hkU : ∀ k ∈ UJ c (J : Matrix (Fin n) (Fin n) L), Iso c (antiJ L n) (antiJ L n) (k : Matrix (Fin n) (Fin n) L) :=
    fun k hk => (iso_cT_cart2 hcc _).2 (by rw [← hJe]; exact hk)
  obtain ⟨g₁, hg₁, e₁⟩ := surj _ (hkU k₁ hk₁.1)
  obtain ⟨g₂, hg₂, e₂⟩ := surj _ (hkU k₂ hk₂.1)
  have memK : ∀ (x : G) (k : GL (Fin n) L), x ∈ U → Φ x = k → k ∈ GLint (Fin n) (intL L) → x ∈ K := by
    intro x k hx ex hk
    have einv : Φ x⁻¹ = ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      calc Φ x⁻¹ = Φ x⁻¹ * (Φ x * ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
            rw [ex, Units.mul_inv, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    refine (hK x).2 ⟨hx, fun i j => ?_, fun i j => ?_⟩
    · rw [ex]; exact P.cartan_entries_of_mem _ _ hk i j
    · rw [einv]; exact P.cartan_entries_of_mem _ _ (inv_mem hk) i j
  refine ⟨g₁, memK _ _ hg₁ e₁ hk₁.2, g₂, memK _ _ hg₂ e₂ hk₂.2,
    inj _ (inv_mem hh) _ (mul_mem (mul_mem hg₁ hh) hg₂) ?_⟩
  have e' := congrArg (fun x : GL (Fin n) L => (x : Matrix (Fin n) (Fin n) L)) e
  simp only [Units.val_mul] at e'
  rw [map_mul, map_mul, e₁, e₂, ← eg h⁻¹, map_inv]
  exact e'

end Abstract

theorem cartanSt2 : CartanSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW _ v w hw hh
  have hσ := hB.cm
  have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw hu hc hW
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ d) a.1 := hg
  have one : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (piE hu) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let Φ : UA σ W.J →* Matrix (Fin d) (Fin d) (w.adicCompletion E) :=
    { toFun := fun g => (a⁻¹).1 * (mat g).map (piE hu) * a.1
      map_one' := by
        rw [show mat (1 : UA σ W.J) = 1 from rfl, one, Matrix.mul_one, Units.inv_mul]
      map_mul' := fun g g' => by
        rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.map_mul]
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left] }
  have hΦ : ∀ g, Φ g = (a⁻¹).1 * (mat g).map (piE hu) * a.1 := fun _ => rfl
  have hint : ∀ g, (∀ i j, Valued.v (Φ g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := fun g => by
    rw [stab_iff hw hu ha]
    exact Iff.rfl
  refine inv_mem_KgK_cart2 hU (USub σ W v) Φ (fun g => ?_) (fun g hg g' hg' e => ?_) (fun N hN => ?_) _ (fun g => ?_) hh
  · have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE hu)) := by
      unfold Iso
      rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
      exact Matrix.ext fun i j => piE_incl hu _
    rw [hΦ]
    exact (iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai)
  · have e1 : (mat g).map (piE hu) = (mat g').map (piE hu) := by
      have e2 := congrArg (fun N => a.1 * N * (a⁻¹).1) e
      simpa [hΦ, Matrix.mul_assoc] using e2
    refine Subtype.ext (Units.ext (mat_inj hw hu ?_ e1))
    have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
    rwa [sub_sub_sub_cancel_right] at this
  · have h2 := (hai.mul ((iso_smul_iff hl _ _).2 hN)).mul (hai.inv a.mul_inv)
    have h3 := h2.isUnit_det (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((map_ne_zero _).2 (PositivityTheory.ThKH.Iwas.det_ne_zero hW)).isUnit)
    obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
    refine ⟨k, hk, ?_⟩
    rw [hΦ, ek]
    simp [Matrix.mul_assoc]
  · rw [hint, hint]
    exact and_congr Iff.rfl ⟨fun H => ⟨fun y hy => (H y hy).1, fun y hy => (H y hy).2⟩, fun H y hy => ⟨H.1 y hy, H.2 y hy⟩⟩

end PositivityTheory.Sph

end
end

-- bundled from Development.WeilBound.ThetaLifts.SphericalLattices.LocModSt
section
noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Loc

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (m : ℕ)

def GW : Subgroup (GL (Fin m ⊕ Fin m) L) where
  carrier := {g | Iso c (Wm L (Fin m)) (Wm L (Fin m)) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)}
  one_mem' := by
    show Iso c _ _ ((1 : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    simp [Iso, Matrix.map_one _ (map_zero c) (map_one c)]
  mul_mem' := fun {a b} ha hb => by
    show Iso c _ _ ((a * b : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    rw [Units.val_mul]; exact Iso.mul ha hb
  inv_mem' := fun {a} ha => by
    show Iso c _ _ ((a⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact Iso.inv ha (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

def IntGL : Subgroup (GL (Fin m ⊕ Fin m) L) := (Matrix.GeneralLinearGroup.map (intL L).subtype).range

def KW : Subgroup (GL (Fin m ⊕ Fin m) L) := GW L c m ⊓ IntGL L m

def PW : Subgroup (GL (Fin m ⊕ Fin m) L) :=
  GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m))

abbrev KPW : Subgroup (GL (Fin m ⊕ Fin m) L) := PW L c m ⊓ KW L c m

def levM (t : GL (Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L :=
  fromBlocks (t : Matrix (Fin m) (Fin m) L) 0 0 (((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c)

def lev : GL (Fin m) L →* GL (Fin m ⊕ Fin m) L where
  toFun t := ⟨levM L c m t, levM L c m t⁻¹,
    by
      have h1 : (t : Matrix (Fin m) (Fin m) L) * ((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) = 1 := Units.mul_inv t
      simp only [levM, fromBlocks_multiply, inv_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [h1, ← Matrix.map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one,
        Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one],
    by
      have h2 : ((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) * (t : Matrix (Fin m) (Fin m) L) = 1 := Units.inv_mul t
      simp only [levM, fromBlocks_multiply, inv_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [h2, ← Matrix.map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one,
        Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one]⟩
  map_one' := by
    ext1
    simp [levM, Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one]
  map_mul' s t := by
    ext1
    simp only [Units.val_mul, levM, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]

def zW (x : Lˣ) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks ((x : L) • 1) 0 0 (((x⁻¹ : Lˣ) : L) • 1), fromBlocks (((x⁻¹ : Lˣ) : L) • 1) 0 0 ((x : L) • 1),
    by simp [fromBlocks_multiply, smul_smul, fromBlocks_one],
    by simp [fromBlocks_multiply, smul_smul, fromBlocks_one]⟩

def LocModSt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q →
    ∀ (m : ℕ), ∀ p ∈ PW L c m,
      ((((KPW L c m).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ) =
        (q : ℝ) ^ (-(2 * (m : ℤ) * ordL (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₁₁.det)) *
        ((((KPW L c m).map (MulAut.conj p).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ)

end Loc

end PositivityTheory.Sph.M2

end
end


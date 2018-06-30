fgi_mod!{
    type Stream = (
        rec stream. Thk[?] (
                {?;?} F
                    (+ Unit +
                        (x Nm[?] x Nat x stream))
            )
    );

    fn cons_stream:(
        Thk[?]
            0 Nm[?] ->
            0 Nat ->
            0 Stream ->
            {?;?} F Stream
    ) = {
        #n.#h.#t. thk n ret roll inj2 (n, h, t)
    }
}

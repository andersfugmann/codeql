class C
    # Should generate 100 + 100 local use-use flow steps for `x`, and not 100 * 100
    #
    # Generated by quick-evaling `gen/0` below:
    #
    # ```ql
    # string gen(int depth) {
    #   depth in [0 .. 100] and
    #   (
    #     if depth = 0
    #     then result = ""
    #     else result = "if (@prop > " + depth + ") then " + gen(depth - 1) + " else use(x) end"
    #   )
    # }
    #
    # string gen() { result = "x = 0\n" + gen(100) + "\n" + gen(100) }
    # ```
    def m()
        x = 0
        if (@prop > 100) then if (@prop > 99) then if (@prop > 98) then if (@prop > 97) then if (@prop > 96) then if (@prop > 95) then if (@prop > 94) then if (@prop > 93) then if (@prop > 92) then if (@prop > 91) then if (@prop > 90) then if (@prop > 89) then if (@prop > 88) then if (@prop > 87) then if (@prop > 86) then if (@prop > 85) then if (@prop > 84) then if (@prop > 83) then if (@prop > 82) then if (@prop > 81) then if (@prop > 80) then if (@prop > 79) then if (@prop > 78) then if (@prop > 77) then if (@prop > 76) then if (@prop > 75) then if (@prop > 74) then if (@prop > 73) then if (@prop > 72) then if (@prop > 71) then if (@prop > 70) then if (@prop > 69) then if (@prop > 68) then if (@prop > 67) then if (@prop > 66) then if (@prop > 65) then if (@prop > 64) then if (@prop > 63) then if (@prop > 62) then if (@prop > 61) then if (@prop > 60) then if (@prop > 59) then if (@prop > 58) then if (@prop > 57) then if (@prop > 56) then if (@prop > 55) then if (@prop > 54) then if (@prop > 53) then if (@prop > 52) then if (@prop > 51) then if (@prop > 50) then if (@prop > 49) then if (@prop > 48) then if (@prop > 47) then if (@prop > 46) then if (@prop > 45) then if (@prop > 44) then if (@prop > 43) then if (@prop > 42) then if (@prop > 41) then if (@prop > 40) then if (@prop > 39) then if (@prop > 38) then if (@prop > 37) then if (@prop > 36) then if (@prop > 35) then if (@prop > 34) then if (@prop > 33) then if (@prop > 32) then if (@prop > 31) then if (@prop > 30) then if (@prop > 29) then if (@prop > 28) then if (@prop > 27) then if (@prop > 26) then if (@prop > 25) then if (@prop > 24) then if (@prop > 23) then if (@prop > 22) then if (@prop > 21) then if (@prop > 20) then if (@prop > 19) then if (@prop > 18) then if (@prop > 17) then if (@prop > 16) then if (@prop > 15) then if (@prop > 14) then if (@prop > 13) then if (@prop > 12) then if (@prop > 11) then if (@prop > 10) then if (@prop > 9) then if (@prop > 8) then if (@prop > 7) then if (@prop > 6) then if (@prop > 5) then if (@prop > 4) then if (@prop > 3) then if (@prop > 2) then if (@prop > 1) then  else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end
        if (@prop > 100) then if (@prop > 99) then if (@prop > 98) then if (@prop > 97) then if (@prop > 96) then if (@prop > 95) then if (@prop > 94) then if (@prop > 93) then if (@prop > 92) then if (@prop > 91) then if (@prop > 90) then if (@prop > 89) then if (@prop > 88) then if (@prop > 87) then if (@prop > 86) then if (@prop > 85) then if (@prop > 84) then if (@prop > 83) then if (@prop > 82) then if (@prop > 81) then if (@prop > 80) then if (@prop > 79) then if (@prop > 78) then if (@prop > 77) then if (@prop > 76) then if (@prop > 75) then if (@prop > 74) then if (@prop > 73) then if (@prop > 72) then if (@prop > 71) then if (@prop > 70) then if (@prop > 69) then if (@prop > 68) then if (@prop > 67) then if (@prop > 66) then if (@prop > 65) then if (@prop > 64) then if (@prop > 63) then if (@prop > 62) then if (@prop > 61) then if (@prop > 60) then if (@prop > 59) then if (@prop > 58) then if (@prop > 57) then if (@prop > 56) then if (@prop > 55) then if (@prop > 54) then if (@prop > 53) then if (@prop > 52) then if (@prop > 51) then if (@prop > 50) then if (@prop > 49) then if (@prop > 48) then if (@prop > 47) then if (@prop > 46) then if (@prop > 45) then if (@prop > 44) then if (@prop > 43) then if (@prop > 42) then if (@prop > 41) then if (@prop > 40) then if (@prop > 39) then if (@prop > 38) then if (@prop > 37) then if (@prop > 36) then if (@prop > 35) then if (@prop > 34) then if (@prop > 33) then if (@prop > 32) then if (@prop > 31) then if (@prop > 30) then if (@prop > 29) then if (@prop > 28) then if (@prop > 27) then if (@prop > 26) then if (@prop > 25) then if (@prop > 24) then if (@prop > 23) then if (@prop > 22) then if (@prop > 21) then if (@prop > 20) then if (@prop > 19) then if (@prop > 18) then if (@prop > 17) then if (@prop > 16) then if (@prop > 15) then if (@prop > 14) then if (@prop > 13) then if (@prop > 12) then if (@prop > 11) then if (@prop > 10) then if (@prop > 9) then if (@prop > 8) then if (@prop > 7) then if (@prop > 6) then if (@prop > 5) then if (@prop > 4) then if (@prop > 3) then if (@prop > 2) then if (@prop > 1) then  else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end else use(x) end
    end

    def use(i)
    end
end

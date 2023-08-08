const EmptyError = error{};
//    ^^^^^^^^^^ (type)(error{})

const SomeError = error{
    //^^^^^^^^^ (type)(error{OutOfMemory,OutOfOrder,OutOfTheBox})
    OutOfMemory,
    OutOfOrder,
    OutOfTheBox,
};

const ParseResult = error{ Overflow, InvalidCharacter }!u32;
//    ^^^^^^^^^^^ (type)(error{Overflow,InvalidCharacter}!u32)

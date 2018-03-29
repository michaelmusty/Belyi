s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,3,6]-8-311111-332-g0";
s`BelyiDBFilename := "8T50-[8,3,6]-8-311111-332-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 6, 8, 3, 1, 5, 2, 7 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ],
[ 5, 7, 4, 3, 6, 1, 8, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 6, 8, 3, 1, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 5, 7, 4, 3, 6, 1, 8, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 6, 8, 3, 1, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 5, 7, 4, 3, 6, 1, 8, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 4, 6, 8, 3, 1, 5, 2, 7 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 5, 7, 4, 3, 6, 1, 8, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 1, 8, 3, 4, 2, 6, 7, 5 ],
[ 2, 1, 5, 3, 4, 8, 6, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 6, 8, 3, 1, 5, 2, 7 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ],
[ 5, 7, 4, 3, 6, 1, 8, 2 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;

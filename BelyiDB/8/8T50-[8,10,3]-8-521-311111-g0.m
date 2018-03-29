s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[8,10,3]-8-521-311111-g0";
s`BelyiDBFilename := "8T50-[8,10,3]-8-521-311111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 10, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 3, 8, 4, 5, 6, 7, 2, 1 ],
[ 1, 8, 7, 3, 4, 5, 6, 2 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 8, 4, 5, 6, 7, 2, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 4, 5, 6, 7, 2, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 4, 5, 6, 7, 2, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 2, 4, 3, 1, 5, 6, 7 ],
[ 1, 5, 2, 4, 3, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 4, 5, 6, 7, 2, 1 ],
\[ 1, 8, 7, 3, 4, 5, 6, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 1, 4, 3, 5, 2, 6, 7 ],
[ 1, 2, 6, 4, 3, 5, 7, 8 ]
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
[ 3, 8, 4, 5, 6, 7, 2, 1 ],
[ 1, 8, 7, 3, 4, 5, 6, 2 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 4, 1, 5, 3, 6, 7, 8, 2 ],
[ 4, 2, 8, 1, 3, 5, 6, 7 ],
[ 2, 3, 1, 4, 5, 6, 7, 8 ]
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

s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[6,6,4]-332-332-44-g1";
s`BelyiDBFilename := "8T50-[6,6,4]-332-332-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 5, 4, 7, 8, 1, 3, 2 ],
[ 5, 6, 1, 7, 3, 2, 8, 4 ],
[ 2, 7, 4, 5, 6, 3, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 7, 8, 1, 3, 2 ],
\[ 5, 6, 1, 7, 3, 2, 8, 4 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 5, 4, 7, 8, 1, 3, 2 ],
\[ 5, 6, 1, 7, 3, 2, 8, 4 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 6, 5, 4, 7, 8, 1, 3, 2 ],
\[ 5, 6, 1, 7, 3, 2, 8, 4 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 > |
[ 5, 4, 8, 7, 6, 1, 2, 3 ],
[ 2, 6, 7, 8, 3, 1, 5, 4 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 6, 5, 4, 7, 8, 1, 3, 2 ],
\[ 5, 6, 1, 7, 3, 2, 8, 4 ],
\[ 2, 7, 4, 5, 6, 3, 8, 1 ]:
 Order := 40320 > |
[ 8, 3, 7, 5, 4, 1, 2, 6 ],
[ 5, 6, 7, 2, 1, 4, 8, 3 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
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
[ 6, 5, 4, 7, 8, 1, 3, 2 ],
[ 5, 6, 1, 7, 3, 2, 8, 4 ],
[ 2, 7, 4, 5, 6, 3, 8, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 1, 6, 7, 3, 5, 8, 4 ],
[ 7, 6, 1, 5, 8, 2, 3, 4 ],
[ 6, 3, 4, 5, 2, 7, 8, 1 ]
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

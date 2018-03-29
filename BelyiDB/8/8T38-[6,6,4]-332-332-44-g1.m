s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T38-[6,6,4]-332-332-44-g1";
s`BelyiDBFilename := "8T38-[6,6,4]-332-332-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 8, 1, 7, 6, 4, 5, 3, 2 ],
[ 5, 7, 4, 6, 1, 3, 8, 2 ],
[ 8, 7, 2, 1, 4, 3, 6, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 1, 7, 6, 4, 5, 3, 2 ],
\[ 5, 7, 4, 6, 1, 3, 8, 2 ],
\[ 8, 7, 2, 1, 4, 3, 6, 5 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 1, 7, 6, 4, 5, 3, 2 ],
\[ 5, 7, 4, 6, 1, 3, 8, 2 ],
\[ 8, 7, 2, 1, 4, 3, 6, 5 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 1, 7, 6, 4, 5, 3, 2 ],
\[ 5, 7, 4, 6, 1, 3, 8, 2 ],
\[ 8, 7, 2, 1, 4, 3, 6, 5 ]:
 Order := 192 > |
[ 4, 1, 7, 2, 8, 5, 3, 6 ],
[ 5, 3, 4, 2, 1, 7, 8, 6 ],
[ 4, 3, 6, 5, 8, 7, 2, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ]:
 Order := 192 > |
[ 8, 1, 7, 6, 4, 5, 3, 2 ],
[ 5, 7, 4, 6, 1, 3, 8, 2 ],
[ 8, 7, 2, 1, 4, 3, 6, 5 ]
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

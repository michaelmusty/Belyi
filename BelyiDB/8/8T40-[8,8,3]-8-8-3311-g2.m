s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T40-[8,8,3]-8-8-3311-g2";
s`BelyiDBFilename := "8T40-[8,8,3]-8-8-3311-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 5, 2, 3, 8, 1, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 1, 3, 2, 8, 5, 7, 6, 4 ]:
 Order := 192 > |
[ 8, 5, 2, 7, 4, 1, 6, 3 ],
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 4, 1, 3, 2, 8, 5, 7, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 5, 2, 7, 4, 1, 6, 3 ],
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 4, 1, 3, 2, 8, 5, 7, 6 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 5, 2, 7, 4, 1, 6, 3 ],
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 4, 1, 3, 2, 8, 5, 7, 6 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 5, 2, 7, 4, 1, 6, 3 ],
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 4, 1, 3, 2, 8, 5, 7, 6 ]:
 Order := 192 > |
[ 8, 5, 2, 7, 4, 1, 6, 3 ],
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 4, 1, 3, 2, 8, 5, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 8, 5, 2, 7, 4, 1, 6, 3 ],
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 4, 1, 3, 2, 8, 5, 7, 6 ]:
 Order := 192 > |
[ 8, 5, 2, 7, 4, 1, 6, 3 ],
[ 7, 5, 8, 2, 3, 1, 4, 6 ],
[ 8, 5, 3, 2, 4, 1, 7, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 2, 3, 8, 1, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 1, 3, 2, 8, 5, 7, 6, 4 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 5, 2, 3, 8, 1, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 1, 3, 2, 8, 5, 7, 6, 4 ]:
 Order := 192 > |
[ 8, 5, 2, 7, 4, 1, 6, 3 ],
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 4, 1, 3, 2, 8, 5, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 5, 2, 3, 8, 1, 6, 7, 4 ],
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 1, 3, 2, 8, 5, 7, 6, 4 ]:
 Order := 192 > |
[ 8, 5, 2, 7, 4, 1, 6, 3 ],
[ 7, 5, 8, 2, 3, 1, 4, 6 ],
[ 8, 5, 3, 2, 4, 1, 7, 6 ]
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
